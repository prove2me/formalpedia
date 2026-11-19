-- Prove2me | Theorems.Thm_DeletionCode_RandomHash_joint_uniform
-- name    : DeletionCode.RandomHash.joint_uniform
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:37:18.917205+00:00
-- url     : https://prove2.me/theorems/8f41c2a9-7368-4252-afc8-2438bb330e9a
-- title:
--   Random Hash: joint uniform
-- statement:
--   Rational independence of the actual integer rows gives a joint uniform
--   circle law, with no rank or measure-preservation premise supplied by callers.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L20-L23
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L20-L23

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]

theorem DeletionCode.RandomHash.joint_uniform (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) :
    MeasurePreserving (jointHash w) volume volume := by sorry
