-- Prove2me | Theorems.Thm_Arxiv2012_05254_triad_image_true_up_to_shift
-- name    : Arxiv2012_05254.triad_image_true_up_to_shift
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T04:38:27.852691+00:00
-- url     : https://prove2.me/theorems/2e882304-e047-4ca6-b15e-544fca03c467
-- title:
--   App. 3: without amplitude errors, the three-fringe image of a closed triad is the true image up to a shift
-- statement:
--   Let $x_0,x_1,x_2$ be the positions of a closed triad of non-collinear elements, with true visibilities $V_{ab}$. Let the element gains $G_a$ have unit modulus: there are no element amplitude errors and no baseline-based errors. Let $\tilde V_{ab}=G_a^*G_bV_{ab}$. Then there is a vector $t$ such that the three-fringe image made from the corrupted visibilities is the true three-fringe image translated by $t$:
--
--   $$\tilde I_3(\hat s)=I_3(\hat s+t)\quad\text{for all }\hat s.$$
--
--   So, without amplitude calibration errors, the image of a closed triad formed from phase-uncalibrated visibilities is the true image, up to a shift.
-- source:
--   Thyagarajan and Carilli, A Geometric View of Closure Phases in Interferometry, arXiv:2012.05254v3, Publ. Astron. Soc. Aust. 38 (2021), claim c028; Appendix 3, last paragraph, PDF p. 18; Abstract, PDF p. 1

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Arxiv2012_05254

theorem triad_image_true_up_to_shift (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x)
    (V : Fin 3 → Fin 3 → ℂ) (G : Fin 3 → ℂ) (hG : ∀ a, ‖G a‖ = 1) :
    ∃ t : Plane, ∀ s : Plane, triadImage x (corruptVis G V) id s = triadImage x V id (s + t) := by sorry

end Arxiv2012_05254
