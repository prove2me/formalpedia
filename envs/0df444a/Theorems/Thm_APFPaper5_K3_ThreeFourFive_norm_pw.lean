-- Prove2me | Theorems.Thm_APFPaper5_K3_ThreeFourFive_norm_pw
-- name    : APFPaper5.K3.ThreeFourFive.norm_pw
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T06:29:09.668183+00:00
-- url     : https://prove2.me/theorems/c263d7c0-fc3d-48dc-aeb0-9abc66b798a0
-- title:
--   norm pw
-- statement:
--   Result: norm pw. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem norm_pw (n : ℕ) : (pw n).1 ^ 2 + (pw n).2 ^ 2 = 25 ^ n
--   ```
--
--   Module context and limits: Integer recurrences for powers of 3+4i prove nonzero coordinates, distinct rational-circle points and no finite state realization of that orbit. Injective self-maps on finite types are periodic. The angle is chosen; density, a continuum, physical states and K3 are not established.
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K3_the_345_turn_never_returns_and_never_turns_a_side_over:102; pullbacks v46; source SHA-256 e73854102ad9e697e4bfaad3364866c49b0773357cf47209b364d0dccad08f7f']

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

theorem APFPaper5.K3.ThreeFourFive.norm_pw :
∀ (n : Nat),
  @Eq.{1} Int
    (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
      (@HPow.hPow.{0, 0, 0} Int Nat Int
        (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
        (@Prod.fst.{0, 0} Int Int (APFPaper5.K3.ThreeFourFive.pw n))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HPow.hPow.{0, 0, 0} Int Nat Int
        (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
        (@Prod.snd.{0, 0} Int Int (APFPaper5.K3.ThreeFourFive.pw n))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@HPow.hPow.{0, 0, 0} Int Nat Int
      (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
      (@OfNat.ofNat.{0} Int (nat_lit 25) (@instOfNat (nat_lit 25))) n) := by sorry
