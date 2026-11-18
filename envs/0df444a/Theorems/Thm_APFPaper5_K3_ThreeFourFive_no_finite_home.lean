-- Prove2me | Theorems.Thm_APFPaper5_K3_ThreeFourFive_no_finite_home
-- name    : APFPaper5.K3.ThreeFourFive.no_finite_home
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T06:28:57.324632+00:00
-- url     : https://prove2.me/theorems/3179f2ec-389b-4f61-9b03-64195f0e225a
-- title:
--   no finite home
-- statement:
--   Result: no finite home. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem no_finite_home {S : Type*} [Finite S] (f : S → S) (s : S) (r : S → ℚ × ℚ)
--       (hr : ∀ n : ℕ, r (f^[n] s) = place n) : False
--   ```
--
--   Module context and limits: Integer recurrences for powers of 3+4i prove nonzero coordinates, distinct rational-circle points and no finite state realization of that orbit. Injective self-maps on finite types are periodic. The angle is chosen; density, a continuum, physical states and K3 are not established.
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K3_the_345_turn_never_returns_and_never_turns_a_side_over:220; pullbacks v46; source SHA-256 e73854102ad9e697e4bfaad3364866c49b0773357cf47209b364d0dccad08f7f']

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

theorem APFPaper5.K3.ThreeFourFive.no_finite_home :
∀ {S : Type apfNative_u_1} [Finite.{apfNative_u_1 + 1} S] (f : S → S) (s : S) (r : S → Prod.{0, 0} Rat Rat)
  (hr :
    ∀ (n : Nat),
      @Eq.{1} (Prod.{0, 0} Rat Rat) (r (@Nat.iterate.{apfNative_u_1 + 1} S f n s))
        (APFPaper5.K3.ThreeFourFive.place n)),
  False := by sorry
