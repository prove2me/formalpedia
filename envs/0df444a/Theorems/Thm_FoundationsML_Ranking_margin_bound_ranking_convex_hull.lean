-- Prove2me | Theorems.Thm_FoundationsML_Ranking_margin_bound_ranking_convex_hull
-- name    : FoundationsML.Ranking.margin_bound_ranking_convex_hull
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-20T04:04:59.982355+00:00
-- url     : https://prove2.me/theorems/a9f66796-39d0-432b-804e-517c919c1b2b
-- title:
--   Corollary 10.4 — Ranking margin bound for the convex hull
-- statement:
--   **Statement (Corollary 10.4, p. 250, PDF p. 267).** Let $H$ be a set of real-valued
--   functions. Fix $\rho>0$; then, for any $\delta>0$, with probability at least $1-\delta$
--   over the choice of a sample $S$ of size $m$, for all $h\in\mathrm{conv}(H)$:
--   $R(h) \le \hat R_{S,\rho}(h) + \tfrac2\rho(R_m^{D_1}(H)+R_m^{D_2}(H)) +
--   \sqrt{\log(1/\delta)/(2m)}$. Theorem 10.1 applied to `conv(H)`, giving RankBoost (whose
--   output is a convex combination up to normalization) a margin-based generalization
--   guarantee independent of the number of boosting rounds.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 250, Corollary 10.4 (PDF p. 267)

import Mathlib
import Definitions.Def_FoundationsML_Ranking_GeneralizationError
import Definitions.Def_FoundationsML_Ranking_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_Ranking_RademacherComplexity
import Definitions.Def_FoundationsML_Ranking_ConvHull

open MeasureTheory

namespace FoundationsML.Ranking

/-- Corollary 10.4 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd
ed., MIT Press 2018, p. 250, PDF p. 267). Let `H` be a set of real-valued functions. Fix
`ρ > 0`; then, for any `δ > 0`, with probability at least `1 − δ` over the choice of a sample
`S` of size `m`, the following ranking guarantee holds for all `h ∈ conv(H)`:
`R(h) ≤ R̂_{S,ρ}(h) + (2/ρ)(R_m^{D1}(H) + R_m^{D2}(H)) + sqrt(log(1/δ)/(2m))`. -/
theorem margin_bound_ranking_convex_hull
    {X : Type*} [MeasurableSpace X] (D : Measure (X × X)) [IsProbabilityMeasure D]
    (f : X × X → ℝ) (hf : ∀ p, f p = 1 ∨ f p = -1) (H : Set (X → ℝ))
    (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × X | ∀ h ∈ ConvHull H,
        GeneralizationError D f h ≤
          EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) (fun i => f (S i)) h +
            (2 / ρ) * (RademacherComplexity (Measure.map Prod.fst D) H m +
              RademacherComplexity (Measure.map Prod.snd D) H m) +
            Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.Ranking
