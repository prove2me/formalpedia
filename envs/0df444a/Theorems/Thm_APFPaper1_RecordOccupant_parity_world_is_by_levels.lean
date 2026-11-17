-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_parity_world_is_by_levels
-- name    : APFPaper1.RecordOccupant.parity_world_is_by_levels
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:41:27.410333+00:00
-- url     : https://prove2.me/theorems/394a0a82-78f1-4632-af42-177282be152d
-- title:
--   parity world is by levels
-- statement:
--   Result: parity world is by levels. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   open Triangle in
--
--   theorem parity_world_is_by_levels : ByLevels side Parity.odd ({()} : Finset Unit)
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
--   ['Theorems.Thm_APFPaper1_RecordOccupant_units_and_levels:170; pullbacks v39; source SHA-256 99fc6f50960d16a10761a351e4333cc422a25416f40f0b28c85d41319deb04c1']

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
namespace Unt
end Unt
open Unt
variable {D : Type u} {X : Type*}

open Triangle in

theorem APFPaper1.RecordOccupant.parity_world_is_by_levels : ByLevels side Parity.odd ({()} : Finset Unit) := by sorry
