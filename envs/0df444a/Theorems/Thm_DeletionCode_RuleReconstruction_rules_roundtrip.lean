-- Prove2me | Theorems.Thm_DeletionCode_RuleReconstruction_rules_roundtrip
-- name    : DeletionCode.RuleReconstruction.rules_roundtrip
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:19:36.509901+00:00
-- url     : https://prove2.me/theorems/276a1c28-d988-46f6-b918-99229c99bec2
-- title:
--   Rule Reconstruction: rules roundtrip
-- statement:
--   Recovering finite word data suffices to determine the entire signed rule set.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RuleReconstruction.lean#L92-L98
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RuleReconstruction.lean#L92-L98

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_RecordSerialization
import Definitions.Def_DeletionCode_RuleReconstruction
set_option autoImplicit true
open DeletionCode DeletionCode.RuleReconstruction
open Windows HeaderRecovery RootSelection SignedSupport RecordSerialization GeneratingModel
open scoped BigOperators

theorem DeletionCode.RuleReconstruction.rules_roundtrip {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) : rulesOfData k group (dataOfFamily E) = rulesOfFamily E group := by sorry
