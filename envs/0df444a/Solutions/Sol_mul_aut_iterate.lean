-- Prove2me | solution 1 for mul_aut_iterate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:19:29.660393+00:00
-- url     : https://prove2.me/submissions/9861b1e6-d5ef-4e4e-95ba-9ef2144b7d0e

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


lemma mul_aut_iterate_oai {G: Type*} [Group G] (f: MulAut G) (n: ℕ): f^[n] = ⇑(f ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    ext a
    rw [Function.iterate_succ_apply, pow_succ, MulAut.mul_apply, ← ih]
end

theorem solution.{u_3} : type_of% @mul_aut_iterate_oai.{u_3} := @mul_aut_iterate_oai.{u_3}
