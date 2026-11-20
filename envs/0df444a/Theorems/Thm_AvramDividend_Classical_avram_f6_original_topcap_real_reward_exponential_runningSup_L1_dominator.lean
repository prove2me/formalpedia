-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_topcap_real_reward_exponential_runningSup_L1_dominator
-- name    : AvramDividend.Classical.avram_f6_original_topcap_real_reward_exponential_runningSup_L1_dominator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:41:58.363189+00:00
-- url     : https://prove2.me/theorems/205b0037-ca58-4a02-9dcf-51efc6512e59
-- title:
--   Original true topcap physical reward uniformly dominated by integrable exponential runningSup plus actual full cash
-- statement:
--   For any original Lévy and true dividend D, if the exact HJB w has a genuine exponential growth upper bound and the true runningSup exponential and full discounted Stieltjes cash are integrable, all actual subordinate rightmesh topcap w(W) plus original cash are uniformly dominated in L1 by K exp(θx) exp(θ runningSup X T)+Full.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_topcap_real_reward_exponential_runningSup_L1_dominator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (hwneg : ∀ y < 0, w y = 0)
    (hwpos : ∀ y : ℝ, 0 ≤ y → 0 ≤ w y)
    (θ K : ℝ) (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hwGrowth : ∀ y, 0 ≤ y → w y ≤ K * Real.exp (θ * y))
    (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (ρ : ℕ → Ω → ℝ≥0) (hρτ : ∀ m ω, ρ m ω ≤ τ ω)
    (Full : Ω → ℝ)
    (hFull : ∀ ω, Full ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal)
    (hFullI : Integrable Full P)
    (hExpI : Integrable (fun ω => Real.exp (θ * runningSup X T ω)) P)
    (Approx : ℕ → Ω → ℝ)
    (hApprox : ∀ m ω, Approx m ω =
      Real.exp (-(q * (ρ m ω : ℝ))) *
        w (if ρ m ω = 0 ∨ (ρ m ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (ρ m ω) ω - rightLimit D (ρ m ω) ω
          else riskProcess X x D (ρ m ω) ω) +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ m ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal) :
    ∃ B : Ω → ℝ, Integrable B P ∧
      ∀ m ω, |Approx m ω| ≤ B ω := by sorry
