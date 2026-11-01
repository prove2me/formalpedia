-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_attains_subunrestricted_level
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_discount_attains_subunrestricted_level
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:30:53.646242+00:00
-- url     : https://prove2.me/theorems/a56d5c83-5f8e-413e-a484-2fd0663c1bd2
-- title:
--   Every discounted killed first-record survival level below unrestricted survival is attained by a positive reflected drawdown depth
-- statement:
--   Fix a positive record height h, positive q, the actual spectrally negative Levy first-record and reflected drawdown times, and pure infinite-small-jump variation. As depth a runs over positive real numbers, the genuine killed discounted record survival runs continuously between its zero-depth limit 0 and its infinite-depth limit exp(-h phi(q)); hence every r strictly between those endpoints is attained at a finite positive drawdown depth. The continuity is the proven original-process depth continuity, equivalently its proven exponential hazard and continuously varying K(a). No Standing or independent excursion assumption.
-- source:
--   Original killed record depth limits e877e7b4-16d8-4b74-8ec2-11fffd3d5fdb and 80304468-d3a4-4d91-a3de-a0b777e0405f; original source K continuity ec9e934a-2ad2-4a0d-8d6e-9dd9654ab798; exact uncapped exponential law 1f5b13d3-98f1-4b35-b1d2-5df29b3cf596; real IVT.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_log_rate_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_exponential_hazard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_tendsto_zero_depth
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_depth_tendsto_unrestricted_root
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_discount_attains_subunrestricted_level
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (h : ℝ) (hh : 0 < h)
    (r : ℝ) (hr0 : 0 < r) (hr : r < Real.exp (-(h * φ))) :
    ∃ a : ℝ, 0 < a ∧
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal = r := by sorry
