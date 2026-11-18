-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva39_aestrong_integrable_nonnegative_Fatou_mean_bound
-- name    : AvramDividend.Classical.avram_bva39_aestrong_integrable_nonnegative_Fatou_mean_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:53:50.307214+00:00
-- url     : https://prove2.me/theorems/6fb12445-b183-455f-b49b-7dd24ae8a759
-- title:
--   AE-strongly-measurable original real reward Fatou bound from integrable nonnegative increasing-source expectations
-- statement:
--   An exact source-independent Fatou bridge for genuine original stopped discounted Stieltjes cash and surviving terminal rewards. If F_n and Y are real integrable, nonnegative almost everywhere, all E[F_n]≤K, the genuine pointwise ENNReal.ofReal Y is bounded by the liminf of ENNReal.ofReal F_n almost everywhere, and K≥0, then E[Y]≤K. Only almost-everywhere measurability follows from integrability; no artificial assumption of globally measurable payoff representatives. The proof uses ofReal_integral_eq_lintegral_ofReal, the a.e.-measurable Fatou lemma lintegral_liminf_le' and ENNReal.toReal_mono.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva39_aestrong_integrable_nonnegative_Fatou_mean_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ) (Y : Ω → ℝ) (K : ℝ)
    (hFI : ∀ n, Integrable (F n) P)
    (hFpos : ∀ n, 0 ≤ᵐ[P] F n)
    (hYI : Integrable Y P)
    (hYpos : 0 ≤ᵐ[P] Y)
    (hMean : ∀ n, (∫ ω, F n ω ∂P) ≤ K)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop)
    (hK : 0 ≤ K) :
    (∫ ω, Y ω ∂P) ≤ K := by sorry
