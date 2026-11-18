-- Prove2me | Theorems.Thm_APFPaper5_K3_ThreeFourFive_pw_mod
-- name    : APFPaper5.K3.ThreeFourFive.pw_mod
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T06:45:47.525761+00:00
-- url     : https://prove2.me/theorems/d8931b3c-eb93-4e39-b692-5ff865d14a02
-- title:
--   pw mod
-- statement:
--   Result: pw mod. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem pw_mod (n : ℕ) :
--       ∃ k l : ℤ, (pw (n + 1)).1 = 3 + 5 * k ∧ (pw (n + 1)).2 = 4 + 5 * l
--   ```
--
--   Module context and limits: Integer recurrences for powers of 3+4i prove nonzero coordinates, distinct rational-circle points and no finite state realization of that orbit. Injective self-maps on finite types are periodic. The angle is chosen; density, a continuum, physical states and K3 are not established.
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K3_the_345_turn_never_returns_and_never_turns_a_side_over:76; pullbacks v46; source SHA-256 e73854102ad9e697e4bfaad3364866c49b0773357cf47209b364d0dccad08f7f']

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

theorem APFPaper5.K3.ThreeFourFive.pw_mod :
∀ (n : Nat),
  @Exists.{1} Int fun (k : Int) =>
    @Exists.{1} Int fun (l : Int) =>
      And
        (@Eq.{1} Int
          (@Prod.fst.{0, 0} Int Int
            (APFPaper5.K3.ThreeFourFive.pw
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3)))
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
              (@OfNat.ofNat.{0} Int (nat_lit 5) (@instOfNat (nat_lit 5))) k)))
        (@Eq.{1} Int
          (@Prod.snd.{0, 0} Int Int
            (APFPaper5.K3.ThreeFourFive.pw
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
              (@OfNat.ofNat.{0} Int (nat_lit 5) (@instOfNat (nat_lit 5))) l))) := by sorry
