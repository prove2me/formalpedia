-- Prove2me | Theorems.Thm_ESL_f_hat_injective
-- name    : ESL.f_hat_injective
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T20:08:45.725969+00:00
-- url     : https://prove2.me/theorems/5d768027-e529-4b58-8a00-998fa8f0957b
-- title:
--   The descended inclusion of the disk classes is injective, by Goldsmith (Lemma 3.2)
-- statement:
--   The descended inclusion of the disk classes is injective: if two link-homotopy classes of pure braids of the disk have the same image on the surface, they are equal. Indeed, a class mapped to the trivial class is represented by a pure braid whose image on the surface is link-homotopically trivial; by the disk-triviality theorem of Goldsmith the braid itself is link-homotopically trivial on the disk, so its class is trivial. This is Lemma 3.2 of the paper.
-- source:
--   J. R. T. Theodoro de Lima, An exact sequence for generalized string links over surfaces, LAJM - Latin-American Journal of Mathematics 2 (2023) no. 1, Section 3 (Lemma 3.2).

import Mathlib
import Definitions.Def_ESL_alg
import Definitions.Def_ESL_tor

namespace ESL

/-!  Milestone 4 (Lemma 3.2): the induced homomorphism f-hat is injective.
A pure braid of the disk whose class maps to the trivial class on the
surface has its image in the trivial subgroup of the surface, so the
Goldsmith disk-triviality property forces the braid itself to be trivial on
the disk, and its class is trivial. -/
theorem f_hat_injective {n : ℕ} {PB_D PB_M HhatD HhatM Pi : Type*}
    [Group PB_D] [Group PB_M] [Group HhatD] [Group HhatM] [Group Pi]
    (W : StringLinkExactWorld n PB_D PB_M HhatD HhatM Pi) :
    ∀ fhat : HhatD →* HhatM, (∀ x : PB_D, fhat (W.qD x) = W.qM (W.f x)) →
      ∀ y z : HhatD, fhat y = fhat z → y = z := by sorry

end ESL
