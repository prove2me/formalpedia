-- Prove2me | Theorems.Thm_ESL_kernel_in_closure
-- name    : ESL.kernel_in_closure
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T20:09:47.557994+00:00
-- url     : https://prove2.me/theorems/6fdb068d-033f-48a7-bda5-ef7393a51b35
-- title:
--   The kernel of the descended loop-reading map lies in the normal closure of the disk classes (Lemma 3.4)
-- statement:
--   The kernel of the descended loop-reading map is contained in the normal closure of the image of the descended inclusion: a class killed by the descended map is represented by a pure braid whose loop tuple is trivial, and by Goldberg's kernel characterization such a braid is a product of conjugates of images of disk braids; pushing this expression through the descent squares exhibits the class inside the normal closure. This is Lemma 3.4 of the paper.
-- source:
--   J. R. T. Theodoro de Lima, An exact sequence for generalized string links over surfaces, LAJM - Latin-American Journal of Mathematics 2 (2023) no. 1, Section 3 (Lemma 3.4).

import Mathlib
import Definitions.Def_ESL_alg
import Definitions.Def_ESL_tor

namespace ESL

/-!  Milestone 6 (Lemma 3.4): the kernel of theta-hat is contained in the
normal closure of the image of f-hat. A class killed by theta-hat is
represented by a pure braid whose theta_n image is trivial; by Goldberg's
theorem such a braid lies in the normal closure of the image of f_n, and
passing to the quotient exhibits the class in the normal closure of the
image of f-hat. -/
theorem kernel_in_closure {n : ℕ} {PB_D PB_M HhatD HhatM Pi : Type*}
    [Group PB_D] [Group PB_M] [Group HhatD] [Group HhatM] [Group Pi]
    (W : StringLinkExactWorld n PB_D PB_M HhatD HhatM Pi) :
    ∀ fhat : HhatD →* HhatM, (∀ x : PB_D, fhat (W.qD x) = W.qM (W.f x)) →
      ∀ thetahat : HhatM →* Pi, (∀ x : PB_M, thetahat (W.qM x) = W.theta x) →
        MonoidHom.ker thetahat ≤ Subgroup.normalClosure (Set.range fhat) := by sorry

end ESL
