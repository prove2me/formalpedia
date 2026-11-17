-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_isRelation_of_same_or_opposite
-- name    : APFPaper1.RecordOccupant.isRelation_of_same_or_opposite
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:39:24.510451+00:00
-- url     : https://prove2.me/theorems/05c80261-9c58-4ce3-96b5-15492e6c7f67
-- title:
--   isRelation of same or opposite
-- statement:
--   Result: isRelation of same or opposite. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem isRelation_of_same_or_opposite (c : Bool) : IsRelation (fun a b => (a != b) = c)
--   ```
--
--   Module context and limits: IsRelation exposes three ordinary Boolean conditions: common-complement invariance, settling neither argument, and excluding at least one pair. They imply same/opposite sides and are proved for those examples. Unt builds XOR units recursively; ByLevels is an explicit, uninstalled predicate. Its parity witness and reading factorization do not establish physical K4.
--
--   Source scope parameters:
--
--   ```lean
--   universe u
--   variable {D : Type u} {X : Type*}
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper1_RecordOccupant_units_and_levels:82; pullbacks v39; source SHA-256 99fc6f50960d16a10761a351e4333cc422a25416f40f0b28c85d41319deb04c1']

import Definitions.Def_APFPaper1_RecordOccupant_units_and_levels_Vocabulary
import Definitions.Def_APFPaper1_RecordOccupant_three_way_relation_Vocabulary
import Theorems.Thm_APFPaper1_RecordOccupant_Parity_every_combination_held
import Theorems.Thm_APFPaper1_RecordOccupant_Parity_members_raw
import Theorems.Thm_APFPaper1_RecordOccupant_Parity_pairs_unsettled
import Theorems.Thm_APFPaper1_RecordOccupant_Parity_triple_settled
import Theorems.Thm_APFPaper1_RecordOccupant_Parity_turnover_keeps_pair_relations
import Theorems.Thm_APFPaper1_RecordOccupant_Parity_turnover_breaks_record
import Theorems.Thm_APFPaper1_RecordOccupant_Parity_is_pair_relation_one_level_up

set_option autoImplicit false

universe u

namespace APFPaper1.RecordOccupant
end APFPaper1.RecordOccupant
open APFPaper1
open APFPaper1.RecordOccupant

theorem APFPaper1.RecordOccupant.isRelation_of_same_or_opposite (c : Bool) : IsRelation (fun a b => (a != b) = c) := by sorry
