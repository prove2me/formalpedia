-- Prove2me | Theorems.Thm_FoundationsML_Boosting_ensemble_rademacher_margin_bound
-- name    : FoundationsML.Boosting.ensemble_rademacher_margin_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:11:45.444999+00:00
-- url     : https://prove2.me/theorems/c45a1ceb-24b5-4fcf-bba0-a6cf14d0fd7e
-- title:
--   Corollary 7.5 — Ensemble Rademacher margin bound (milestone)
-- statement:
--   **Statement (Corollary 7.5, p. 158, PDF p. 175).** Let $H$ denote a set of real-valued
--   functions. Fix $\rho>0$. Then, for any $\delta>0$, with probability at least $1-\delta$,
--   each of the following holds for all $h\in\mathrm{conv}(H)$:
--   $$R(h) \le \hat R_{S,\rho}(h) + \frac2\rho R_m(H) + \sqrt{\frac{\log(1/\delta)}{2m}}$$
--   $$R(h) \le \hat R_{S,\rho}(h) + \frac2\rho \hat R_S(H) + 3\sqrt{\frac{\log(2/\delta)}{2m}}.$$
--
--   This applies Theorem 5.8's margin bound to $\mathrm{conv}(H)$ and rewrites the resulting
--   Rademacher-complexity terms via Lemma 7.4, giving a margin bound for convex-combination
--   ensembles (such as AdaBoost's own normalized output $\bar f$) in terms of the base
--   classifier set $H$'s own complexity, not the (much larger) $\mathrm{conv}(H)$'s.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 158, Corollary 7.5 (PDF p. 175)

import Mathlib
import Definitions.Def_FoundationsML_Boosting_MarginGeneralizationError
import Definitions.Def_FoundationsML_Boosting_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_Boosting_RademacherComplexity
import Definitions.Def_FoundationsML_Boosting_ConvHull

open MeasureTheory

namespace FoundationsML.Boosting

/-- Corollary 7.5 (Ensemble Rademacher margin bound; Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 158, PDF p. 175). Let `H` denote
a set of real-valued functions. Fix `ρ > 0`; then, for any `δ > 0`, with probability at least
`1 − δ`, each of the following holds for all `h ∈ conv(H)`:
`R(h) ≤ R̂_{S,ρ}(h) + (2/ρ) R_m(H) + sqrt(log(1/δ)/(2m))` and
`R(h) ≤ R̂_{S,ρ}(h) + (2/ρ) R̂_S(H) + 3·sqrt(log(2/δ)/(2m))`.

**Formalization Note.** This is Theorem 5.8's margin bound (restated locally in `Boosting`,
since drafts cannot import another chunk's draft module) applied to `conv(H)`, then rewritten
via Lemma 7.4 so its Rademacher-complexity terms are `H`'s own (not `conv(H)`'s) — matching the
book's final displayed form of Corollary 7.5, quoted verbatim in `BRIEF.md`. As in the SVM
chunk's `margin_bound_binary_classification`, `D.map Prod.fst` is the marginal of `D` on `X`. -/
theorem ensemble_rademacher_margin_bound
    {X : Type*} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (hDfst : Measurable (Prod.fst : X × ℝ → X))
    (H : Set (X → ℝ)) (hHmeas : ∀ h ∈ ConvHull H, Measurable h)
    (m : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ ConvHull H,
        (MarginGeneralizationError D h ≤
           EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) h +
             (2 / ρ) * RademacherComplexity (D.map Prod.fst) H m +
             Real.sqrt (Real.log (1 / δ) / (2 * m))) ∧
        (MarginGeneralizationError D h ≤
           EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) h +
             (2 / ρ) * EmpiricalRademacherComplexity H (fun i => (S i).1) +
             3 * Real.sqrt (Real.log (2 / δ) / (2 * m)))}).toReal := by sorry

end FoundationsML.Boosting
