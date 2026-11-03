-- Prove2me | solution 1 for toIntLinearMap_comp_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:21:30.414423+00:00
-- url     : https://prove2.me/submissions/ae578756-fdd8-46f4-9d6e-869dab26bf33

import Mathlib

section
-- module Solutions.OAIQ093_PR.Unipotent_FG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Finite generation of subgroups

That subgroups of finitely generated abelian and nilpotent groups are finitely generated, plus
the supporting transfer lemmas along homomorphisms.
-/


set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false

open scoped commutatorElement IsMulCommutative Pointwise

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)


lemma toIntLinearMap_comp_mul_oai {M : Type*}  [AddCommGroup M] (f g : M →+ M): ((f.comp g).toIntLinearMap) = f.toIntLinearMap * g.toIntLinearMap := by
  ext a
  simp
end

theorem solution.{u_3} : type_of% @toIntLinearMap_comp_mul_oai.{u_3} := @toIntLinearMap_comp_mul_oai.{u_3}
