-- Prove2me | Theorems.Thm_APFPaper5_K3_ThreeFourFive_returns_of_finite
-- name    : APFPaper5.K3.ThreeFourFive.returns_of_finite
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T06:45:50.748131+00:00
-- url     : https://prove2.me/theorems/a39ce1e7-7276-4b6d-98c7-97543c5fe0ce
-- title:
--   returns of finite
-- statement:
--   Result: returns of finite. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem returns_of_finite {S : Type*} [Finite S] (f : S → S) (hf : Function.Injective f) :
--       ∃ n : ℕ, 1 ≤ n ∧ f^[n] = id
--   ```
--
--   Module context and limits: Integer recurrences for powers of 3+4i prove nonzero coordinates, distinct rational-circle points and no finite state realization of that orbit. Injective self-maps on finite types are periodic. The angle is chosen; density, a continuum, physical states and K3 are not established.
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K3_the_345_turn_never_returns_and_never_turns_a_side_over:198; pullbacks v46; source SHA-256 e73854102ad9e697e4bfaad3364866c49b0773357cf47209b364d0dccad08f7f']

import Definitions.Def_APFPaper5_K3_the_345_turn_never_returns_and_never_turns_a_side_over_Vocabulary
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finite.Prod
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
set_option autoImplicit false
universe apfNative_u_1

theorem APFPaper5.K3.ThreeFourFive.returns_of_finite :
∀ {S : Type apfNative_u_1} [Finite.{apfNative_u_1 + 1} S] (f : S → S)
  (hf : @Function.Injective.{apfNative_u_1 + 1, apfNative_u_1 + 1} S S f),
  @Exists.{1} Nat fun (n : Nat) =>
    And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n)
      (@Eq.{apfNative_u_1 + 1} (S → S) (@Nat.iterate.{apfNative_u_1 + 1} S f n) (@id.{apfNative_u_1 + 1} S)) := by sorry
