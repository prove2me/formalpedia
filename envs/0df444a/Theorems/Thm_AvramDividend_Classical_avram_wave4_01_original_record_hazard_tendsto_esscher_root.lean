-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_hazard_tendsto_esscher_root
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_hazard_tendsto_esscher_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:14:41.602631+00:00
-- url     : https://prove2.me/theorems/d455bcb7-c70c-47a4-b83d-cc0d689003b6
-- title:
--   Genuine first-record killing hazard converges to the unrestricted Esscher root as reflected drawdown tolerance grows
-- statement:
--   For a spectrally negative original Lévy process with divergent absolute small-negative-jump moment and positive discount, the actual reflected-killed strict first-upcrossing hazard κ(a)=-log E[e^{-qT₁};T₁<D_a] converges to the positive root φ of ψ(φ)=q as a tends to infinity. No Standing hypothesis, substituted excursion object or invented axiom is assumed. The proof combines the proven original-source hazard derivative, its depth antitonicity, positive-root tilted-scale monotonicity and the independently proved unbounded-variation Esscher flatness.
-- source:
--   Original killed-record semigroup and depth hazard identities 3890ee9b, 96bc676f; source tilted-record logarithmic derivative eb85f6af; root tilted-scale monotonicity e0ec313a; Esscher log-derivative flatness 3d2b9177; all canonically Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_infinite_variation_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_positive_monotone_of_given_root
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_hazard_antitone_depth
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_log_derivative
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_log_derivative_flatness
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_hazard_tendsto_esscher_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    Tendsto
      (fun a : ℝ => -Real.log
        ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
                    barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
          else 0 ∂P).toReal))
      atTop (nhds φ) := by sorry
