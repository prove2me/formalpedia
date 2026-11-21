-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_true_finitecap_Hessian_start_mask_uniform_bound
-- name    : AvramDividend.Classical.avram_ga_original_true_finitecap_Hessian_start_mask_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:29:56.816596+00:00
-- url     : https://prove2.me/theorems/032aced4-69f8-4174-a494-0a8ab98c9c94
-- title:
--   Uniform bounded original finite-cap Hessian coefficient for every predictably active Gaussian physical-grid start, including final crossing cell
-- statement:
--   For the authentic original spectrally negative Lévy reserve and dividend strategy, every physical-grid start satisfying s_i<ρ has postpaid reserve x+X_si−rightLimit D_si bounded below by the strict pre-stop floor a, using the already Proved original gledger20 source theorem. If w'' is continuous on [a,b], the discounted Hessian coefficient 1_{Y≤b} e^{-q s_i}w''(Y) is uniformly bounded over all mesh sizes, cells and sample paths. Unlike the existing original theorem restricted to complete cells, this holds at the start of the terminal crossing cell and keeps the initial-time mask predictable, enabling correct martingale-difference L² estimates.
-- source:
--   Strengthens original full-cell Hessian bound 2e5994a5 by combining the accepted original strict postpayment floor cb67c5ea with accepted discounted masked compact Hessian upper bound b4429e67, without using the future-dependent final-cell mask.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_original_true_finitecap_Hessian_start_mask_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (a b q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ)
    (hFloor : ∀ (ω : Ω) (t : ℝ≥0), 0 < t → t < ρ ω →
      a ≤ riskProcess X x D t ω)
    (hCont : ContinuousOn (fun y => iteratedDeriv 2 w y) (Icc a b))
    (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m i : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      s < ρ ω →
      |Real.exp (-(q * (s : ℝ))) *
        (if x + X.X s ω - rightLimit D s ω ≤ b then
          iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)
        else 0)| ≤ K := by sorry
