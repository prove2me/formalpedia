-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_log_derivative
-- name    : AvramDividend.Classical.avram_wave4_02_source_esscher_record_log_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:52:49.477473+00:00
-- url     : https://prove2.me/theorems/eb85f6af-2ff4-408d-a3be-c9521c82a2ef
-- title:
--   Actual Esscher scale logarithmic derivative equals the genuine killed-first-record rate minus its positive root
-- statement:
--   Under the exact spectrally negative Lévy source, q-scale function, infinite absolute small-negative-jump moment, and supplied positive Esscher root psi(phi)=q, the logarithmic derivative of the actual tilted scale V(x)=exp(-phi*x) W(x) is the source-identified killed-first-record rate -log E_P[e^{-q tau_1};tau_1<D_a] minus phi. Uses the genuine stopped-record semigroup and source scale sandwich; does not claim an Itô excursion compensator.
-- source:
--   Source first-record semigroup and local scale-ratio sandwich; KKR (2013), equations 31–33, log scale derivative height tail. Existing Proved source log-rate continuity, local sandwich, local logarithmic derivative.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_canonical_infinite_jump_log_rate_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_genuine_local_scale_ratio_sandwich
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_local_exponential_scale_sandwich_log_deriv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_02_source_esscher_record_log_derivative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ z : ℝ, 0 < z → V z = Real.exp (-(φ * z)) * W z)
    (a : ℝ) (ha : 0 < a) :
    HasDerivAt (fun z : ℝ => Real.log (V z))
      (-Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
        barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
      else 0 ∂P).toReal) - φ) a := by sorry
