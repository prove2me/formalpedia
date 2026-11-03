-- Prove2me | solution 1 for toIntLinearMap_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:22:00.637261+00:00
-- url     : https://prove2.me/submissions/62388eb4-16f2-445f-ba2e-c88bf8d25e62

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


lemma toIntLinearMap_pow_apply_oai {M : Type*}  [AddCommGroup M]  (f : M →+ M) (g: M) (n: ℕ): ((f.toIntLinearMap)^(n)) g = (f^[n]) g := by
  induction n generalizing g with
  | zero =>
    simp
  | succ n ih =>
    rw [pow_succ]
    rw [Function.iterate_succ]
    simp
    rw [ih]
end

theorem solution.{u_3} : type_of% @toIntLinearMap_pow_apply_oai.{u_3} := @toIntLinearMap_pow_apply_oai.{u_3}
