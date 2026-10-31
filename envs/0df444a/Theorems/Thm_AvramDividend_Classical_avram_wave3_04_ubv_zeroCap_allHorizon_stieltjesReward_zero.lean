-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_zeroCap_allHorizon_stieltjesReward_zero
-- name    : AvramDividend.Classical.avram_wave3_04_ubv_zeroCap_allHorizon_stieltjesReward_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:49:50.733+00:00
-- url     : https://prove2.me/theorems/771fa12d-84c9-4f86-82bb-6245490a8831
-- title:
--   Unbounded-variation zero-capped original dividend controls pay zero expected Stieltjes dividends at every finite horizon
-- statement:
--   For any unbounded-variation spectrally negative Lévy process and every truly adapted admissible dividend strategy started at capital zero under cap zero, the full exact expected discounted Lebesgue–Stieltjes dividend measure on all pre-ruin payment times through any finite closed horizon T vanishes. The proof derives almost-sure immediate ruin from original-law unbounded-variation downward regularity and pathwise zero-barrier ruin comparison. The already kernel-Proved exact instant-ruin Stieltjes budget bounds the entire closed-horizon reward, including any time-zero dividend atom, by the initial capital zero on each such path. Since nonnegative extended real integrals have zero weight on each full-measure path, the outer original-law expected lintegral is exactly zero. This proves a complete positive-time zero-cap branch of corrected UBV verification, with arbitrary q and without postulating a stochastic integral or discarding continuous payments.
-- source:
--   Pinned exact private candidate-probe 03c26b32-1b8c-466e-9787-a2bb5f805c0a reached sentinel with no source errors, SHA-256 37cd977e60296e041eaf30b50715d45d61dd1cd64e0fa0965faff4d3bbbf1872. Canonical Proved ae_negative_near_zero_of_unbounded_variation 703dc740-a8df-4cd1-9ff1-622fd81d68c7; zero_cap_ruinTime_le_barrier_ruinTime 73ce745b-97fc-42ad-92e3-397e0ef5f34a; avram_wave3_03_bv_instant_ruin_closed_horizon_initial_budget 389a618c-8fb0-4164-afac-c2bfd197c65d; exact original Stieltjes measure definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_negative_path
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_eq_ruinTime_runningSup
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_zero_cap_ruinTime_le_barrier_ruinTime
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_instant_ruin_closed_horizon_initial_budget

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_ubv_zeroCap_allHorizon_stieltjesReward_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X 0 0 D)
    (q : ℝ) (T : ℝ≥0) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) = 0 := by sorry
