-- Prove2me | Theorems.Thm_APFPaper5_K3_ThreeFourFive_pw_add
-- name    : APFPaper5.K3.ThreeFourFive.pw_add
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T06:45:42.51553+00:00
-- url     : https://prove2.me/theorems/3033e462-8bc4-4c21-b1c9-2b0caa64d2b2
-- title:
--   pw add
-- statement:
--   Result: pw add. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem pw_add (m k : ℕ) :
--       (pw (m + k)).1 = (pw m).1 * (pw k).1 - (pw m).2 * (pw k).2 ∧
--         (pw (m + k)).2 = (pw m).1 * (pw k).2 + (pw m).2 * (pw k).1
--   ```
--
--   Module context and limits: Integer recurrences for powers of 3+4i prove nonzero coordinates, distinct rational-circle points and no finite state realization of that orbit. Injective self-maps on finite types are periodic. The angle is chosen; density, a continuum, physical states and K3 are not established.
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K3_the_345_turn_never_returns_and_never_turns_a_side_over:111; pullbacks v46; source SHA-256 e73854102ad9e697e4bfaad3364866c49b0773357cf47209b364d0dccad08f7f']

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

theorem APFPaper5.K3.ThreeFourFive.pw_add :
∀ (m k : Nat),
  And
    (@Eq.{1} Int
      (@Prod.fst.{0, 0} Int Int
        (APFPaper5.K3.ThreeFourFive.pw (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m k)))
      (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@Prod.fst.{0, 0} Int Int (APFPaper5.K3.ThreeFourFive.pw m))
          (@Prod.fst.{0, 0} Int Int (APFPaper5.K3.ThreeFourFive.pw k)))
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@Prod.snd.{0, 0} Int Int (APFPaper5.K3.ThreeFourFive.pw m))
          (@Prod.snd.{0, 0} Int Int (APFPaper5.K3.ThreeFourFive.pw k)))))
    (@Eq.{1} Int
      (@Prod.snd.{0, 0} Int Int
        (APFPaper5.K3.ThreeFourFive.pw (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m k)))
      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@Prod.fst.{0, 0} Int Int (APFPaper5.K3.ThreeFourFive.pw m))
          (@Prod.snd.{0, 0} Int Int (APFPaper5.K3.ThreeFourFive.pw k)))
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@Prod.snd.{0, 0} Int Int (APFPaper5.K3.ThreeFourFive.pw m))
          (@Prod.fst.{0, 0} Int Int (APFPaper5.K3.ThreeFourFive.pw k))))) := by sorry
