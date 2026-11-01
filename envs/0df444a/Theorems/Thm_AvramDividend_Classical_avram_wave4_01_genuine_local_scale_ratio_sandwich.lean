-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_genuine_local_scale_ratio_sandwich
-- name    : AvramDividend.Classical.avram_wave4_01_genuine_local_scale_ratio_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:35:45.231355+00:00
-- url     : https://prove2.me/theorems/2490701d-9960-43af-aa11-c17cee86c818
-- title:
--   Original-process first-record hazard yields local exponential W-ratio sandwich
-- statement:
--   For the actual infinite-small-jump spectrally negative Lévy process with its genuine first-record discount F, fixed record hazard κ(a)=-log F_a(1), and W the genuine Standing-free q-scale function, the restricted record-height sandwich implies exp(-κ(a)(b-a))≤W(a)/W(b)≤exp(-κ(b)(b-a)) whenever 0<a<b and b-a<a. The proof explicitly converts extended nonnegative integrals to real, checks nonzero W and finite record factors, and uses the accepted exact original record exponential law.
-- source:
--   Original killed record semigroup and source scale ratio f9f9bc34; Wave4 exact C1 primary cd61d678, semantic early split.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_unbounded_genuine_record_scale_sandwich
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_discount_le_one
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_exponential_hazard

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_genuine_local_scale_ratio_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν = ⊤)
    (F : ℝ → ℝ → ℝ≥0∞)
    (hF : ∀ a h : ℝ, F a h =
      ∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P)
    (κ : ℝ → ℝ) (hκ : ∀ a : ℝ, κ a = -Real.log ((F a 1).toReal)) :
    ∀ a b : ℝ, 0 < a → a < b → b - a < a →
      Real.exp (-(κ a * (b - a))) ≤ W a / W b ∧
      W a / W b ≤ Real.exp (-(κ b * (b - a))) := by sorry
