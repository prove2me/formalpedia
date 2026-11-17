-- Prove2me | Theorems.Thm_APFPaper5_K2_keptClass_union_of_disjoint
-- name    : APFPaper5.K2.keptClass_union_of_disjoint
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:31:58.91061+00:00
-- url     : https://prove2.me/theorems/40274c63-2eab-46d8-9cfc-c545875cdbec
-- title:
--   keptClass union of disjoint
-- statement:
--   Result: keptClass union of disjoint. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem keptClass_union_of_disjoint [DecidableEq D] (keeps : Finset D → W → Bool)
--       (S T : Finset D) (hunion : ∀ a, keeps (S ∪ T) a = (keeps S a || keeps T a))
--       (hdisj : ∀ a, ¬ (keeps S a = true ∧ keeps T a = true)) :
--       keptClass keeps (S ∪ T) = keptClass keeps S + keptClass keeps T
--   ```
--
--   Module context and limits: Active and signed-side classes are mathematical candidates, not adopted state readings. keptClass represents the recorded part only. Hold transformation rules retain RearrangesFamily and the stated flip assumptions; union additivity requires the explicit union rule and disjoint kept records.
--
--   Source scope parameters:
--
--   ```lean
--   universe uI uX uD uW
--   variable {ι : Type uI} {X : Type uX} {D : Type uD} {W : Type uW}
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K2_state_class_candidates:154; pullbacks v39; source SHA-256 72423d5f7c1afb45e6a16aeca09a021c2de8dc1cacc91a639ea111660cfd570c']

import Definitions.Def_APFPaper5_K2_StateClass
import Definitions.Def_APFPaper5_K2_HoldScore
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open APFPaper5.K1

namespace APFPaper5.K2
end APFPaper5.K2
open APFPaper5
open APFPaper5.K2
universe uI uX uD uW
variable {ι : Type uI} {X : Type uX} {D : Type uD} {W : Type uW}





/-! ### K1's table is an overlap of record lists -/





/-! ### Candidate A: the distinctions that read true, added up -/









/-! ### Candidate B: the side of each distinction -/





/-! ### Candidate C: the records the held family keeps -/

theorem APFPaper5.K2.keptClass_union_of_disjoint [DecidableEq D] (keeps : Finset D → W → Bool)
    (S T : Finset D) (hunion : ∀ a, keeps (S ∪ T) a = (keeps S a || keeps T a))
    (hdisj : ∀ a, ¬ (keeps S a = true ∧ keeps T a = true)) :
    keptClass keeps (S ∪ T) = keptClass keeps S + keptClass keeps T := by sorry
