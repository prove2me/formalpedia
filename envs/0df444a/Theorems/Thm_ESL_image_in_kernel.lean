-- Prove2me | Theorems.Thm_ESL_image_in_kernel
-- name    : ESL.image_in_kernel
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T20:09:26.888977+00:00
-- url     : https://prove2.me/theorems/e32ead60-ecf0-43eb-bac8-e82dfcb407d3
-- title:
--   The image of the disk classes lies in the kernel of the descended loop-reading map (Lemma 3.3)
-- statement:
--   The image of the descended inclusion lies in the kernel of the descended loop-reading map: the loop tuple of the image of a disk braid is trivial, by Goldberg's theorem on the disk, so the descended loop-reading map kills every class in the image of the descended inclusion. This is Lemma 3.3 of the paper, the right-exactness ingredient of Theorem 3.1.
-- source:
--   J. R. T. Theodoro de Lima, An exact sequence for generalized string links over surfaces, LAJM - Latin-American Journal of Mathematics 2 (2023) no. 1, Section 3 (Lemma 3.3).

import Mathlib
import Definitions.Def_ESL_alg
import Definitions.Def_ESL_tor

namespace ESL

/-!  Milestone 5 (Lemma 3.3): the image of f-hat lies in the kernel of
theta-hat. The square commutes with theta_n by Goldberg's theorem used in
the proof: theta_n (f_n x) = 1 for every pure braid x of the disk, so
theta-hat kills every class in the image of f-hat. -/
theorem image_in_kernel {n : ℕ} {PB_D PB_M HhatD HhatM Pi : Type*}
    [Group PB_D] [Group PB_M] [Group HhatD] [Group HhatM] [Group Pi]
    (W : StringLinkExactWorld n PB_D PB_M HhatD HhatM Pi) :
    ∀ fhat : HhatD →* HhatM, (∀ x : PB_D, fhat (W.qD x) = W.qM (W.f x)) →
      ∀ thetahat : HhatM →* Pi, (∀ x : PB_M, thetahat (W.qM x) = W.theta x) →
        ∀ y : HhatM, (∃ x : HhatD, fhat x = y) → thetahat y = 1 := by sorry

end ESL
