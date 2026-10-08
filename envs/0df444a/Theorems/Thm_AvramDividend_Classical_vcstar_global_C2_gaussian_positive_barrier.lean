-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_global_C2_gaussian_positive_barrier
-- name    : AvramDividend.Classical.vcstar_global_C2_gaussian_positive_barrier
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T23:16:40.560544+00:00
-- url     : https://prove2.me/theorems/a8fb5c02-0f6f-4f67-b8cc-9d2ebcffe2e3
-- title:
--   Gaussian regularity: globally C2 optimal dividend barrier across its join
-- statement:
--   Gaussian case of global C2 verification regularity for the positive optimal barrier. A positive Gaussian coefficient supplies twice differentiable scale-function smoothness, while the optimal barrier minimises W'. The first derivative matches the affine region at c*, and W''(c*)=0 gives second-order matching. This is the C2 gluing result required by Proposition 4(i) for unbounded-variation processes and is distinct from the existing theorem limited to x<c*.
-- source:
--   Avram, Palmowski and Pistorius (2007), Theorem 2, condition (3.3), Lemma 3(i), second-order smooth fit at Gaussian optimal barrier.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem vcstar_global_C2_gaussian_positive_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hσ : 0 < X.σ) :
    ContDiffOn ℝ 2 (vcstar W) (Ioi 0) := by
  sorry
end AvramDividend.Classical
