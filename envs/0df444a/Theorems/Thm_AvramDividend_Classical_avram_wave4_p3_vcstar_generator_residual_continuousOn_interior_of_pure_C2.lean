-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_residual_continuousOn_interior_of_pure_C2
-- name    : AvramDividend.Classical.avram_wave4_p3_vcstar_generator_residual_continuousOn_interior_of_pure_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:37:10.161643+00:00
-- url     : https://prove2.me/theorems/5eab4b3d-a87c-4189-b63b-dabbbd026a68
-- title:
--   Source Lévy compensated generator residual is continuous throughout the strict positive-barrier interior under pure-jump C2 regularity
-- statement:
--   For the exact q-scale dividend candidate at finite strictly positive optimal barrier, under Standing, sigma=0, unbounded variation and the exact positive-state C2 vcstar hypothesis, the compensated generator residual is continuous at every 0<x<cstar. Use W(0)=0 from infinite small jumps, global continuity and monotonicity of vcstar, and the previously Proved P3 uniform compensated small/far jump dominated-continuity theorem on compact neighborhoods of each interior point. The result supplies a pointwise-continuity interface for a future Laplace-uniqueness or a.e. interior harmonicity route, without itself asserting source harmonicity.
-- source:
--   Avram–Palmowski–Pistorius 2007 Lemma 4 and Standing (3.3); Proved P3 UUID d574f843 compact residual continuity, zero-origin infinite small jumps, global positive barrier continuity and monotonicity. Private pinned candidate-probe proof source work/avram_wave4_p3_pure_C2_interior_residual_continuity_private_probe.lean; no canonical proof status is claimed before remote acceptance.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p3_vcstar_generator_residual_continuousOn_interior_of_pure_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hσ : X.σ = 0) (hnbv : ¬ X.BoundedVariation)
    (hC2 : ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ContinuousOn
      (fun x : ℝ => X.generator (vcstar W) x - q * vcstar W x)
      (Ioo 0 (cstar W).toReal) := by sorry
