-- Prove2me | Theorems.Thm_ESL_f_hat_welldefined
-- name    : ESL.f_hat_welldefined
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:08:23.184081+00:00
-- url     : https://prove2.me/theorems/2c0b5f24-ab95-4f7b-8376-fae84cc903ea
-- title:
--   The inclusion-induced homomorphism descends to the link-homotopy quotients
-- statement:
--   The homomorphism induced by the inclusion of the disk into the surface descends to the link-homotopy quotients: there is an induced homomorphism from the link-homotopy classes of pure braids of the disk to the link-homotopy classes of pure braids of the surface, carrying the class of a pure braid of the disk to the class of its image. The descent is possible because the inclusion carries link-homotopically trivial braids of the disk to link-homotopically trivial braids of the surface.
-- source:
--   J. R. T. Theodoro de Lima, An exact sequence for generalized string links over surfaces, LAJM - Latin-American Journal of Mathematics 2 (2023) no. 1, Section 3 (the construction of the induced map f-hat).

import Mathlib
import Definitions.Def_ESL_alg
import Definitions.Def_ESL_tor

namespace ESL

/-!  Milestone 3: the homomorphism f_n descends to the link-homotopy
quotients. Since f_n carries the trivial pure braids of the disk into the
trivial pure braids of the surface, there is an induced homomorphism
f-hat carrying the class of a pure braid of the disk to the class of its
image, making the square commute. -/
theorem f_hat_welldefined {n : ℕ} {PB_D PB_M HhatD HhatM Pi : Type*}
    [Group PB_D] [Group PB_M] [Group HhatD] [Group HhatM] [Group Pi]
    (W : StringLinkExactWorld n PB_D PB_M HhatD HhatM Pi) :
    ∃ fhat : HhatD →* HhatM, ∀ x : PB_D, fhat (W.qD x) = W.qM (W.f x) := by sorry

end ESL
