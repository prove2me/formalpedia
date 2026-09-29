-- Prove2me | Theorems.Thm_FoundationsML_ModelSelection_erm_bound
-- name    : FoundationsML.ModelSelection.erm_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:21:49.236204+00:00
-- url     : https://prove2.me/theorems/b1b66e86-0289-4926-86c9-a0d3d9cc6c37
-- title:
--   Proposition 4.1 — ERM estimation-error bound
-- statement:
--   **Statement (Proposition 4.1, p. 62, PDF p. 79).** For any sample $S$, the hypothesis
--   $h_S^{ERM}$ minimizing the empirical error over $H$ satisfies
--   $$\Pr\Big[R(h_S^{ERM}) - \inf_{h\in H} R(h) > \epsilon\Big] \le
--   \Pr\Big[\sup_{h\in H}|R(h)-\hat R_S(h)| > \tfrac\epsilon2\Big].$$
--   This reduces bounding ERM's estimation error to a uniform-convergence bound over $H$, the
--   starting point for both the SRM and convex-surrogate-loss sections of the chapter.
--
--   **Formalization Note.** `hERM` is taken as a hypothesis-supplied function satisfying the ERM
--   optimality property (`hERM_mem`, `hERM_min`) rather than constructed via `Classical.choice`
--   over an arbitrary `H`; `H.Nonempty` (`hH`) guards `sInf (GeneralizationError D c '' H)`
--   against trap 5 (an empty image would make the left-hand event vacuously about `-∞`).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 62, Proposition 4.1 (PDF p. 79)

import Mathlib
import Definitions.Def_FoundationsML_ModelSelection_GeneralizationError
import Definitions.Def_FoundationsML_ModelSelection_EmpiricalError

open MeasureTheory

namespace FoundationsML.ModelSelection

/-- Proposition 4.1 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*,
2nd ed., MIT Press 2018, p. 62, PDF p. 79). Let `hERM` be the hypothesis returned by empirical
risk minimization over a nonempty hypothesis set `H`: `hERM S ∈ H` and `hERM S` minimizes the
empirical error `R̂_S(·)` over `H`, for every sample `S`. Then, for any `ε`,
`P[R(h_S^ERM) − inf_{h∈H} R(h) > ε] ≤ P[sup_{h∈H} |R(h) − R̂_S(h)| > ε/2]`, the probability
taken over the draw of `S` from `D^m`. -/
theorem erm_bound {X Y : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (c : X → Y) (H : Set (X → Y)) (hH : H.Nonempty) (m : ℕ)
    (hERM : (Fin m → X) → (X → Y))
    (hERM_mem : ∀ S, hERM S ∈ H)
    (hERM_min : ∀ S, ∀ h ∈ H, EmpiricalError S c (hERM S) ≤ EmpiricalError S c h)
    (ε : ℝ) :
    (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | GeneralizationError D c (hERM S) -
        sInf (GeneralizationError D c '' H) > ε}).toReal ≤
    (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | (⨆ h ∈ H, |GeneralizationError D c h - EmpiricalError S c h|) > ε / 2}
      ).toReal := by sorry

end FoundationsML.ModelSelection
