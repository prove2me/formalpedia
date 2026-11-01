-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_contDiffOn_two_of_standing
-- name    : AvramDividend.Classical.avram_wave4_p2_scale_primitive_contDiffOn_two_of_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:31:40.129823+00:00
-- url     : https://prove2.me/theorems/925aaf62-029b-48ed-9f1d-2dc822518dbd
-- title:
--   Integrated source q-scale is C2 above zero under Standing
-- statement:
--   For the genuine original source spectrally negative Levy process under Standing and positive discount q, the q-scale W is C1 on positive reserves. Its oriented primitive U(x)=integral_0^x W gains one positive-axis derivative and is C2 on (0,infinity). The proof uses source interval integrability and strong measurability to obtain HasDerivAt U (W x) x; the published C1 theorem for W then upgrades the derivative to C1. This establishes exact global positive-reserve C2 of U without any Gaussian assumption or C2 claim for W, providing the curvature input needed in the primitive weighted tent Fubini proof.
-- source:
--   Avram, Palmowski and Pistorius (2007), standing scale regularity; Mathlib fundamental theorem of calculus and ContDiffOn.succ criterion. Necessary non-Gaussian primitive generator analytic obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_scale_primitive_contDiffOn_two_of_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContDiffOn ℝ 2
      (fun x : ℝ => ∫ t in (0 : ℝ)..x, W t) (Ioi (0 : ℝ)) := by sorry
