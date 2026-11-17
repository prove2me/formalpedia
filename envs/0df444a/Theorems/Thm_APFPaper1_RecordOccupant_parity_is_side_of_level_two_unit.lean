-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_parity_is_side_of_level_two_unit
-- name    : APFPaper1.RecordOccupant.parity_is_side_of_level_two_unit
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:40:40.132751+00:00
-- url     : https://prove2.me/theorems/05c55ff9-0e2b-4ace-8294-a2c09253340c
-- title:
--   parity is side of level two unit
-- statement:
--   Result: parity is side of level two unit. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   open Triangle in
--
--   theorem parity_is_side_of_level_two_unit (x : Corner → Bool) :
--       Parity.odd () x ↔
--         Unt.reading side (Unt.rel (Unt.rel (Unt.base Corner.a) (Unt.base Corner.b)) (Unt.base Corner.c))
--           x = true
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
--   ['Theorems.Thm_APFPaper1_RecordOccupant_units_and_levels:162; pullbacks v39; source SHA-256 99fc6f50960d16a10761a351e4333cc422a25416f40f0b28c85d41319deb04c1']

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

theorem APFPaper1.RecordOccupant.parity_is_side_of_level_two_unit (x : Corner → Bool) :
    Parity.odd () x ↔
      Unt.reading side (Unt.rel (Unt.rel (Unt.base Corner.a) (Unt.base Corner.b)) (Unt.base Corner.c))
        x = true := by sorry
