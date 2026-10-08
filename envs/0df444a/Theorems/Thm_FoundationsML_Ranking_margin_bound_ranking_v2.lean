-- Prove2me | Theorems.Thm_FoundationsML_Ranking_margin_bound_ranking_v2
-- name    : FoundationsML.Ranking.margin_bound_ranking_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:19:03.338429+00:00
-- url     : https://prove2.me/theorems/d4f06089-ad0f-44cf-806f-1667f15f2b3c
-- title:
--   Theorem 10.1 — margin bound for ranking (goal; $m\ge1$, bounded measurable $H$)
-- statement:
--   **Statement (Theorem 10.1, p. 242, PDF p. 259).** Let $H$ be a set of real-valued (measurable) functions mapping into a bounded interval and $f$ a $\{-1,+1\}$-valued (measurable) preference function. Fix $\rho>0$; then, for any $\delta\in(0,1)$, with probability at least $1-\delta$ over the choice of a sample $S$ of size $m\ge1$ of pairs drawn i.i.d. from $D$, each of the following holds for all $h\in H$:
--   $$R(h) \le \hat R_{S,\rho}(h) + \tfrac2\rho\big(R_m^{D_1}(H)+R_m^{D_2}(H)\big) + \sqrt{\tfrac{\log(1/\delta)}{2m}}, \qquad (10.5)$$
--   $$R(h) \le \hat R_{S,\rho}(h) + \tfrac2\rho\big(\hat R_{S_1}(H)+\hat R_{S_2}(H)\big) + 3\sqrt{\tfrac{\log(2/\delta)}{2m}}. \qquad (10.6)$$
--   Each inequality holds with probability at least $1-\delta$.
--
--   **Formalization Note.** The retired version allowed $m=0$ (every sample-dependent term is Lean's $x/0=0$). Changes: $m\ge1$, $\delta\in(0,1)$ (standing conventions); $H$ bounded (Definition 3.1's domain for the Rademacher complexities); the book's standing measurability (footnote 2, p. 10) of the functions in $H$ and of $f$, and (footnote 3, p. 30) of the supremum defining $\hat R_S(H)$ (needed for $R_m^{D_1},R_m^{D_2}$ to be the book's expectations rather than Lean's junk $0$) explicit; the corrected `EmpiricalRademacherComplexity`/`RademacherComplexity` (`_v2`, supremum over exactly $H$). As before, $D_1=D.\mathrm{map}\,\mathrm{Prod.fst}$, $D_2=D.\mathrm{map}\,\mathrm{Prod.snd}$ are the two marginals, $S_1,S_2$ the coordinate projections of the pair sample, $y_i=f(x_i,x'_i)$, and the two inequalities are separate probability statements.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 242, Theorem 10.1 (PDF p. 259)

import Mathlib
import Definitions.Def_FoundationsML_Ranking_GeneralizationError
import Definitions.Def_FoundationsML_Ranking_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_Ranking_RademacherComplexity_v2

open MeasureTheory

namespace FoundationsML.Ranking

/-- Theorem 10.1 (Margin bound for ranking; goal; Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 242, PDF p. 259). Let `H` be a
set of real-valued functions (bounded, as Definition 3.1 requires) and `f` a `{−1,+1}`-valued
preference function. Fix `ρ > 0`; then, for any `δ > 0`, with probability at least `1 − δ`
over the choice of a sample `S` of size `m ≥ 1` of pairs from `D`, each of the following
holds for all `h ∈ H`:
`R(h) ≤ R̂_{S,ρ}(h) + (2/ρ)(R_m^{D1}(H) + R_m^{D2}(H)) + sqrt(log(1/δ)/(2m))`   (10.5)
and `R(h) ≤ R̂_{S,ρ}(h) + (2/ρ)(R̂_{S1}(H) + R̂_{S2}(H)) + 3·sqrt(log(2/δ)/(2m))`   (10.6).

**Formalization Note.** Replaces `margin_bound_ranking`, which allowed `m = 0` (every
sample-dependent term is then Lean's `x / 0 = 0`). Changes: `m ≥ 1`, `δ ∈ (0,1)` (standing
conventions); `H` maps into a bounded interval (`hHb`, Definition 3.1's domain for the
Rademacher complexities); the book's standing measurability (footnote 2, p. 10) of the
functions in `H` and of the preference function `f`, and (footnote 3, p. 30) of the supremum
defining `R̂_S(H)` (`hHsup`, needed for `R_m^{D1}`, `R_m^{D2}` to be the book's expectations
rather than Lean's junk `0`) are explicit; the corrected
`EmpiricalRademacherComplexity`/`RademacherComplexity` (`_v2`, supremum over exactly `H`) are
used. As before, `D1 = D.map Prod.fst`, `D2 = D.map Prod.snd` are the two marginals, `S1`, `S2`
the two coordinate projections of the pair sample, and each displayed inequality holds with
probability at least `1 − δ`. -/
theorem margin_bound_ranking_v2
    {X : Type*} [MeasurableSpace X] (D : Measure (X × X)) [IsProbabilityMeasure D]
    (f : X × X → ℝ) (hf : ∀ p, f p = 1 ∨ f p = -1) (hf_meas : Measurable f)
    (H : Set (X → ℝ)) (hHb : ∃ a b : ℝ, ∀ h ∈ H, ∀ x, h x ∈ Set.Icc a b)
    (hHmeas : ∀ h ∈ H, Measurable h)
    (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) (hm : 0 < m)
    (hHsup : Measurable (fun S : Fin m → X => EmpiricalRademacherComplexity H S))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × X | ∀ h ∈ H,
        GeneralizationError D f h ≤
          EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) (fun i => f (S i)) h +
            (2 / ρ) * (RademacherComplexity (Measure.map Prod.fst D) H m +
              RademacherComplexity (Measure.map Prod.snd D) H m) +
            Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal ∧
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × X | ∀ h ∈ H,
        GeneralizationError D f h ≤
          EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) (fun i => f (S i)) h +
            (2 / ρ) * (EmpiricalRademacherComplexity H (fun i => (S i).1) +
              EmpiricalRademacherComplexity H (fun i => (S i).2)) +
            3 * Real.sqrt (Real.log (2 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.Ranking
