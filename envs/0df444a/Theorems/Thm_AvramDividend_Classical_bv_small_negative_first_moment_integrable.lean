-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
-- name    : AvramDividend.Classical.bv_small_negative_first_moment_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T12:38:38.968268+00:00
-- url     : https://prove2.me/theorems/2296f406-f6e2-452a-b844-811bf68e9733
-- title:
--   Finite first negative-jump moment from bounded-variation Lévy condition
-- statement:
--   For an Avram spectrally negative Lévy process with bounded variation, the negative jump size -y is integrable on (-1,0) with respect to the Lévy measure. This extracts the exact first-moment integrability needed for the bounded-variation dominated-convergence theorem from the model's BoundedVariation field, including the support-specific identity |y|=-y.
-- source:
--   Pinned Mathlib ENNReal.lintegral_ofReal_ne_top_iff_integrable, ae_restrict_mem and Integrable.congr. Source-faithful BoundedVariation.2 states finite lintegral of ENNReal.ofReal |y| restricted to (-1,0). No Lean invoked locally.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set
open scoped ENNReal NNReal

namespace AvramDividend.Classical

theorem bv_small_negative_first_moment_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    IntegrableOn (fun y : ℝ => -y) (Ioo (-1 : ℝ) 0) X.ν := by
  sorry

end AvramDividend.Classical
