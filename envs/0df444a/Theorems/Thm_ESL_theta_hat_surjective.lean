-- Prove2me | Theorems.Thm_ESL_theta_hat_surjective
-- name    : ESL.theta_hat_surjective
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T20:07:48.390461+00:00
-- url     : https://prove2.me/theorems/6a3586b3-cfde-45c3-bab9-6ba725eff275
-- title:
--   The descended loop-reading homomorphism is surjective (Lemma 2.14)
-- statement:
--   Every descent of the loop-reading homomorphism to the link-homotopy quotient is surjective: every element of the target group is the loop tuple of some pure braid of the surface, and every class is the class of some pure braid, so every element of the target is the image of some class under the descended map. This is the surjectivity part of Lemma 2.14.
-- source:
--   J. R. T. Theodoro de Lima, An exact sequence for generalized string links over surfaces, LAJM - Latin-American Journal of Mathematics 2 (2023) no. 1, Section 2 (Lemma 2.14, the surjectivity part).

import Mathlib
import Definitions.Def_ESL_alg
import Definitions.Def_ESL_tor

namespace ESL

/-!  Milestone 2 (Lemma 2.14): the induced homomorphism theta-hat from the
link-homotopy classes of pure braids on the surface to the n-fold product
of the fundamental group is surjective. Every element of the product is
the image of a pure braid, and the quotient map is surjective, so the
descent is surjective as well. -/
theorem theta_hat_surjective {n : ℕ} {PB_D PB_M HhatD HhatM Pi : Type*}
    [Group PB_D] [Group PB_M] [Group HhatD] [Group HhatM] [Group Pi]
    (W : StringLinkExactWorld n PB_D PB_M HhatD HhatM Pi) :
    ∀ thetahat : HhatM →* Pi, (∀ x : PB_M, thetahat (W.qM x) = W.theta x) →
      ∀ y : Pi, ∃ c : HhatM, thetahat c = y := by sorry

end ESL
