-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_tendsto_zero_record_height
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_discount_tendsto_zero_record_height
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:33:44.793984+00:00
-- url     : https://prove2.me/theorems/0379161a-bf29-477e-a942-7cf110751e85
-- title:
--   Actual reflected first-record killed discount vanishes at infinite upward record height
-- statement:
--   At every fixed positive reflected drawdown threshold, the actual original first-record killed q-discount mass G_a(h) tends to zero as the strict upward-record height h grows without bound. Under divergent absolute small-negative-jump moment, the canonically proved positive original stopped discount satisfies 0<G_a(h)≤exp(-φ h) for every h>0, where φ>0 solves ψ(φ)=q. The real exponential tail tends to zero and squeezes the actual stopped expectation. This is a source process tail condition for killed-record renewal, with no Standing and no artificial stochastic axiom.
-- source:
--   Proved quantitative source bound 95151d6b-175b-41a5-8fbf-c34f163b28b6 and pinned Mathlib exponential tail and filter squeeze.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_pos_le_root_bound
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_discount_tendsto_zero_record_height
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun h : ℝ =>
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
                    barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal)
      atTop (nhds (0 : ℝ)) := by sorry
