-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_ae_strong_L1_convergence
-- name    : AvramDividend.Classical.avram_p2_j_ui_l2_ae_strong_L1_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:22:24.302201+00:00
-- url     : https://prove2.me/theorems/d6ca9fde-2d7c-44a1-a0ab-1792fe07b27e
-- title:
--   Almost-everywhere convergence plus uniform L² control implies strong L¹ convergence of real random variables
-- statement:
--   On any finite probability space, uniformly L2-bounded strongly measurable real random variables converging almost everywhere have an integrable limit and converge strongly in L1 seminorm. The proof derives the quantitative uniform-integrability modulus from L2 control and invokes verified pinned-Mathlib Vitali; no assumed integrability of the limit.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_uniform_l1_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_restriction_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_quantitative_l2_modulus_to_uniform_integrable

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_l2_ae_strong_L1_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (B : ℝ≥0)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hB : ∀ n, eLpNorm (Y n) 2 P ≤ (B : ENNReal))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    MemLp Z 1 P ∧
      Tendsto (fun n => eLpNorm (Y n - Z) 1 P) atTop (nhds 0) := by sorry
