-- Prove2me | Theorems.Thm_APFPaper5_K3_ThreeFourFive_second_ne_zero
-- name    : APFPaper5.K3.ThreeFourFive.second_ne_zero
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T06:45:52.640607+00:00
-- url     : https://prove2.me/theorems/b900f123-02ba-45bb-8646-52875332494f
-- title:
--   second ne zero
-- statement:
--   Result: second ne zero. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem second_ne_zero (n : ℕ) (hn : 1 ≤ n) : (pw n).2 ≠ 0
--   ```
--
--   Module context and limits: Integer recurrences for powers of 3+4i prove nonzero coordinates, distinct rational-circle points and no finite state realization of that orbit. Injective self-maps on finite types are periodic. The angle is chosen; density, a continuum, physical states and K3 are not established.
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K3_the_345_turn_never_returns_and_never_turns_a_side_over:96; pullbacks v46; source SHA-256 e73854102ad9e697e4bfaad3364866c49b0773357cf47209b364d0dccad08f7f']

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

theorem APFPaper5.K3.ThreeFourFive.second_ne_zero :
∀ (n : Nat) (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n),
  @Ne.{1} Int (@Prod.snd.{0, 0} Int Int (APFPaper5.K3.ThreeFourFive.pw n))
    (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by sorry
