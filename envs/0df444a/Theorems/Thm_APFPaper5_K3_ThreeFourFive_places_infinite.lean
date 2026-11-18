-- Prove2me | Theorems.Thm_APFPaper5_K3_ThreeFourFive_places_infinite
-- name    : APFPaper5.K3.ThreeFourFive.places_infinite
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T06:45:41.638839+00:00
-- url     : https://prove2.me/theorems/ad389065-0b13-4a66-b13e-3a19a47c0031
-- title:
--   places infinite
-- statement:
--   Result: places infinite. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem places_infinite : (Set.range place).Infinite
--   ```
--
--   Module context and limits: Integer recurrences for powers of 3+4i prove nonzero coordinates, distinct rational-circle points and no finite state realization of that orbit. Injective self-maps on finite types are periodic. The angle is chosen; density, a continuum, physical states and K3 are not established.
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K3_the_345_turn_never_returns_and_never_turns_a_side_over:194; pullbacks v46; source SHA-256 e73854102ad9e697e4bfaad3364866c49b0773357cf47209b364d0dccad08f7f']

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

theorem APFPaper5.K3.ThreeFourFive.places_infinite :
@Set.Infinite.{0} (Prod.{0, 0} Rat Rat) (@Set.range.{0, 1} (Prod.{0, 0} Rat Rat) Nat APFPaper5.K3.ThreeFourFive.place) := by sorry
