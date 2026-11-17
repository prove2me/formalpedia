-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_true_stopped_finitecap_Hessian_uniform_of_band
-- name    : AvramDividend.Classical.avram_ga_original_true_stopped_finitecap_Hessian_uniform_of_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T17:48:54.658802+00:00
-- url     : https://prove2.me/theorems/2e5994a5-7df1-40ae-876e-9c83d6e8bbf3
-- title:
--   Original stopped finite-cap Gaussian clipped Hessian has uniform bound from strict floor and C2 band
-- statement:
--   The strict original pre-ruin floor on the prepayment reserve implies the same floor for the postpayment right-limit reserve at every physical-grid start before the stopping clock (already proved gledger20). If the second derivative is continuous on the band from that floor to the upper caplinear cutoff b, its discounted clipped active full-cell coefficient admits a deterministic uniform absolute bound. The theorem is the exact hBound premise for the source-specific Gaussian Hessian L1 result 7e470c61.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology

theorem AvramDividend.Classical.avram_ga_original_true_stopped_finitecap_Hessian_uniform_of_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (a b q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      a ≤ riskProcess X x D t ω)
    (hCont : ContinuousOn (fun y => iteratedDeriv 2 w y) (Icc a b))
    (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) (ω : Ω) (i : ℕ),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      i < m → s < ρ ω → s + Δ ≤ ρ ω →
      |Real.exp (-(q * (s : ℝ))) *
        (if x + X.X s ω - rightLimit D s ω ≤ b
        then iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)
        else 0)| ≤ K := by sorry
