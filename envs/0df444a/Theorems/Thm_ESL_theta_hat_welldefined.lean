-- Prove2me | Theorems.Thm_ESL_theta_hat_welldefined
-- name    : ESL.theta_hat_welldefined
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T20:07:05.848538+00:00
-- url     : https://prove2.me/theorems/1d09d09d-6028-406c-bc9b-a4965e425a85
-- title:
--   The loop-reading homomorphism descends to the link-homotopy quotient (Lemma 2.14)
-- statement:
--   The homomorphism that reads off the loops traced by the strands of a pure braid of the surface descends to the link-homotopy quotient: there is an induced homomorphism from the quotient group of link-homotopy classes to the target group, carrying the class of a pure braid to the loop tuple of the braid itself. The descent is possible because the link-homotopically trivial braids are killed by the loop-reading homomorphism. This is the well-definedness part of Lemma 2.14.
-- source:
--   J. R. T. Theodoro de Lima, An exact sequence for generalized string links over surfaces, LAJM - Latin-American Journal of Mathematics 2 (2023) no. 1, Section 2 (Lemma 2.14, the well-definedness part).

import Mathlib
import Definitions.Def_ESL_alg
import Definitions.Def_ESL_tor

namespace ESL

/-!  Milestone 1: the homomorphism theta_n descends to the
link-homotopy quotient of the pure braid group of the surface. Since the
trivial subgroup is contained in the kernel of theta_n, there is an induced
homomorphism theta-hat carrying the class of a pure braid to its theta_n
image. This is the well-definedness part of Lemma 2.14 of the source
paper. -/
theorem theta_hat_welldefined {n : ℕ} {PB_D PB_M HhatD HhatM Pi : Type*}
    [Group PB_D] [Group PB_M] [Group HhatD] [Group HhatM] [Group Pi]
    (W : StringLinkExactWorld n PB_D PB_M HhatD HhatM Pi) :
    ∃ thetahat : HhatM →* Pi, ∀ x : PB_M, thetahat (W.qM x) = W.theta x := by sorry

end ESL
