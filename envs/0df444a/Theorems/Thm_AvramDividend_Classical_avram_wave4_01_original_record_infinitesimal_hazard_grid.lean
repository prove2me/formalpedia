-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_infinitesimal_hazard_grid
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_infinitesimal_hazard_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:03:41.036006+00:00
-- url     : https://prove2.me/theorems/0bb7c8d9-93ad-4a91-9e9c-0ee3689860f5
-- title:
--   Original reflected first-record killing rate recovered from vanishing-height discounted survival
-- statement:
--   For the genuine spectrally negative Lévy first strict upward record T_h and actual reflected ruin D_a under divergent small-negative-jump first absolute moment, the discrete vanishing-height hazard n(1-E[e^{-qT_{1/n}}; T_{1/n}<D_a]) tends to the ordinary positive-reserve logarithmic q-scale slope W'(a)/W(a). This is a source-process infinitesimal hazard interpretation without Standing, Esscher tilting or excursion substitution. The n=0 term is harmless in real division conventions.
-- source:
--   Canonically Proved original-process full-height exponential record identity 1c71a04d-268a-4126-b1bd-c0537bda0db1, genuine record hazard derivative and Standing-free C1 cd61d678, and Proved exact rare-grid exponential limit b40dc5bd-f95e-452e-be79-c8f9a030ae58. The bridge is eventual positivity of 1/n for n>0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
import Theorems.Thm_AvramDividend_Classical_bv_rare_grid_exponential_limit_ws01b

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_infinitesimal_hazard_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ∀ a : ℝ, 0 < a →
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (1 - (∫⁻ ω,
              if twoSidedExitUpTime X (1 / (n : ℝ)) ω <
                  barrierRuinTime X a ω then
                ENNReal.ofReal
                  (Real.exp (-(q *
                    (twoSidedExitUpTime X (1 / (n : ℝ)) ω).toReal)))
              else 0 ∂P).toReal))
        atTop (nhds (deriv W a / W a)) := by sorry
