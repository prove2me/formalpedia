-- Prove2me | Theorems.Thm_FoundationsML_Regression_finite_hypothesis_regression_bound
-- name    : FoundationsML.Regression.finite_hypothesis_regression_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-20T04:08:44.87929+00:00
-- url     : https://prove2.me/theorems/4cf2e00e-39b5-4969-a78a-b95f38ffe472
-- title:
--   Theorem 11.1 — Finite-hypothesis-set regression bound
-- statement:
--   **Statement (Theorem 11.1, p. 268, PDF p. 285).** Let $L$ be a loss function bounded by
--   $M$. Assume $H$ is finite. Then, for any $\delta>0$, with probability at least $1-\delta$,
--   for all $h\in H$: $R(h) \le \hat R_S(h) + M\sqrt{(\log|H|+\log(1/\delta))/(2m)}$. The
--   regression analogue of chunk `02-pac`'s finite-hypothesis-set classification bound.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 268, Theorem 11.1 (PDF p. 285)

import Mathlib
import Definitions.Def_FoundationsML_Regression_GeneralizationError
import Definitions.Def_FoundationsML_Regression_EmpiricalError

open MeasureTheory

namespace FoundationsML.Regression

/-- Theorem 11.1 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 268, PDF p. 285). Let `L` be a loss function bounded by `M`. Assume the
hypothesis set `H` is finite. Then, for any `δ > 0`, with probability at least `1 − δ`, for
all `h ∈ H`: `R(h) ≤ R̂_S(h) + M sqrt((log|H| + log(1/δ))/(2m))`.

**Formalization Note.** `hLnn : ∀ y y', 0 ≤ L y y'` matches the chapter's standing convention
`L : Y×Y → R+` (p. 284); combined with `hLb`, `L ∈ [0,M]`, and the exact constant `M` (not
`2M`) in the theorem's bound depends on this range having width exactly `M` (the book's proof,
p. 268: "By Hoeffding's inequality, since `L` takes values in `[0, M]`..."). `hH_meas`/`hL_meas`
guard `GeneralizationError`'s Bochner integral against trap 2: without them, an adversarial
`h ∈ H` could make `p ↦ L (h p.1) p.2` non-measurable, junking `GeneralizationError` to `0` and
making the (already `≥0`, by `hLnn`/finite-sum `EmpiricalError`) right-hand side trivially
dominate — for that `h` — without the theorem's real content. -/
theorem finite_hypothesis_regression_bound
    {X : Type*} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (L : ℝ → ℝ → ℝ) (M : ℝ) (hM : 0 < M) (hLnn : ∀ y y', 0 ≤ L y y') (hLb : ∀ y y', L y y' ≤ M)
    (hL_meas : Measurable (Function.uncurry L))
    (H : Finset (X → ℝ)) (hHne : H.Nonempty) (hH_meas : ∀ h ∈ H, Measurable h)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ H,
        GeneralizationError D L h ≤
          EmpiricalError S L h +
            M * Real.sqrt ((Real.log H.card + Real.log (1 / δ)) / (2 * m))}).toReal := by sorry

end FoundationsML.Regression
