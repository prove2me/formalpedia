-- Prove2me | Theorems.Thm_AvramDividend_Classical_integrable_product_signed_jump_of_neg_map
-- name    : AvramDividend.Classical.integrable_product_signed_jump_of_neg_map
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:25:08.975367+00:00
-- url     : https://prove2.me/theorems/cdf9751a-76dd-4a41-8799-980b26e21b26
-- title:
--   Transport product integrability under reflection of the Lévy jump coordinate
-- statement:
--   An integrable function over a product whose second measure is reflected by y↦−y pulls back to an integrable function over the original product measure. The transferred function may agree only almost everywhere with the reflected integrand, as required for negative Lévy jumps.
-- source:
--   Mathlib measure product pushforward and integrability under measurable maps; supports Avram et al. (2007), Lemma 4.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open MeasureTheory

namespace AvramDividend.Classical

theorem integrable_product_signed_jump_of_neg_map
    (μ ν : Measure ℝ) [SFinite ν]
    (F G : ℝ × ℝ → ℝ)
    (hF : Integrable F (μ.prod (ν.map (fun y : ℝ => -y))))
    (hFG : (F ∘ Prod.map (id : ℝ → ℝ) (fun y : ℝ => -y))
      =ᵐ[μ.prod ν] G) :
    Integrable G (μ.prod ν) := by sorry

end AvramDividend.Classical
