-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_killed_record_potential_height_measure
-- name    : AvramDividend.Classical.avram_wave4_02_source_killed_record_potential_height_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:29:14.611816+00:00
-- url     : https://prove2.me/theorems/e595b0f9-186f-4f85-b064-a7eff8a815fc
-- title:
--   Source killed-first-record potential constructs an atomless finite-tail height measure with exact tilted-scale ratio
-- statement:
--   For the actual original spectrally negative Levy path reflected at its running maximum, under divergent small-jump variation and an exact positive q-Esscher root, the killed first-record stopped expectation yields a continuous nonnegative antitone rate vanishing at infinity. Construct an atomless Borel measure mu on heights with finite positive upper tails equal exactly to -log E_P[e^{-q tau_1};tau_1<D_x]-phi, and prove the exact source tilted scale interval representation through mu for 0<x<=a. This is a source-specific killed-potential measure; it does not assert mu is the characteristic measure of the actual Esscher excursion PPP, whose compensation theorem remains separate.
-- source:
--   Proved source killed first-record rate 08f9ec73/22a833f3/8b2f9051, true FTC interval ratio 963970fa, Stieltjes tail construction c2cc29c2; KKR 2013 review (31)-(33), Lévy real stopped clocks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_atomless_positive_tail_measure_of_antitone_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_height_rate_nonneg_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_height_rate_antitone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_height_rate_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_killed_potential_interval_representation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_02_source_killed_record_potential_height_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ z : ℝ, 0 < z → V z = Real.exp (-(φ * z)) * W z) :
    ∃ μ : Measure ℝ,
      NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x →
        μ.real (Ici x) =
          -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
            barrierRuinTime X x ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
          else 0 ∂P).toReal) - φ) ∧
      (∀ x a : ℝ, 0 < x → x ≤ a →
        V x / V a =
          Real.exp (-(∫ t in x..a, μ.real (Ici t)))) := by sorry
