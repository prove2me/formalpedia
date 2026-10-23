-- Prove2me | Theorems.Thm_ESL_exact_sequence
-- name    : ESL.exact_sequence
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:11:11.04692+00:00
-- url     : https://prove2.me/theorems/3a6f64a2-7a97-4ae6-8bb1-7020f526f398
-- title:
--   The exact sequence for generalized string links over surfaces (Theorem 3.1)
-- statement:
--   The exact sequence for generalized string links over surfaces: there are a descended inclusion, from the link-homotopy classes of pure braids of the disk to the link-homotopy classes of pure braids of the surface, and a descended loop-reading map, from the surface classes onto the n-fold product of the fundamental group of the surface, such that the descended inclusion is injective, the descended loop-reading map is surjective, and the kernel of the latter is exactly the normal closure of the image of the former. This is Theorem 3.1 of the paper, extending the exact sequence of Goldberg from the disk to surfaces of genus at least one.
-- source:
--   J. R. T. Theodoro de Lima, An exact sequence for generalized string links over surfaces, LAJM - Latin-American Journal of Mathematics 2 (2023) no. 1, Section 3 (Theorem 3.1, the main theorem).

import Mathlib
import Definitions.Def_ESL_alg
import Definitions.Def_ESL_tor

namespace ESL

/-!  The goal (Theorem 3.1): the exact sequence for generalized string
links over surfaces. There is an exact sequence from the
link-homotopy classes of pure braids of the disk, through the
link-homotopy classes of pure braids of the surface, onto the n-fold
product of the fundamental group of the surface: the induced map f-hat is
injective by Lemma 3.2, the induced map theta-hat is surjective by Lemma
2.14, and the kernel of theta-hat is the normal closure of the image of
f-hat by Lemmas 3.3 and 3.4. -/
theorem exact_sequence {n : ℕ} {PB_D PB_M HhatD HhatM Pi : Type*}
    [Group PB_D] [Group PB_M] [Group HhatD] [Group HhatM] [Group Pi]
    (W : StringLinkExactWorld n PB_D PB_M HhatD HhatM Pi) :
    ∃ fhat : HhatD →* HhatM, ∃ thetahat : HhatM →* Pi,
      (∀ x : PB_D, fhat (W.qD x) = W.qM (W.f x)) ∧
      (∀ x : PB_M, thetahat (W.qM x) = W.theta x) ∧
      (∀ y z : HhatD, fhat y = fhat z → y = z) ∧
      (∀ y : Pi, ∃ c : HhatM, thetahat c = y) ∧
      MonoidHom.ker thetahat = Subgroup.normalClosure (Set.range fhat) := by sorry

end ESL
