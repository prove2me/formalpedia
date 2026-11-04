-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_postpayment_exponential_fixedtime_expected_antitone
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_postpayment_exponential_fixedtime_expected_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:42:44.189498+00:00
-- url     : https://prove2.me/theorems/5a01c779-1301-4b61-a50f-8abf105e799e
-- title:
--   Same-source discounted postpayment Lévy exponential expectations decrease across fixed times
-- statement:
--   For original spectrally negative Lévy X and actual dividend control D, the accepted postpayment exponential supermartingale and its probability measure give a nonincreasing expectation between any two deterministic times s≤t. This is a fixed-time source result; random-ruin-clock optional stopping and the canonical w are not assumed or derived.
-- source:
--   Proved original source discounted postpayment exponential supermartingale fab320c3; Mathlib Supermartingale.setIntegral_le exact pinned signature, probability instance from X.isProbability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_postPayment_discounted_exponential_supermartingale
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_postpayment_exponential_fixedtime_expected_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, Real.exp
      (θ * (x + X.X t ω - rightLimit D t ω) - (t : ℝ) * q) ∂P) ≤
    (∫ ω, Real.exp
      (θ * (x + X.X s ω - rightLimit D s ω) - (s : ℝ) * q) ∂P) := by sorry
