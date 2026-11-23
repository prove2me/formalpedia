-- Prove2me | Theorems.Thm_Comp_ModelData_pre1F_eq
-- name    : Comp.ModelData.pre1F_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:53:02.598275+00:00
-- url     : https://prove2.me/theorems/ef518b24-81cf-4614-af00-258756e654d1
-- title:
--   Model Data: pre1 F eq
-- statement:
--   The transfer lemma: the general operator and the row-based one agree. `supportF_eq` rewritten
--       under the two quantifiers, which is all there is to it -- both have the same shape.
--
--       Note what this does *not* do: narrow the action quantifiers to the state's enabled actions.
--       That is sound for this operator but not piecewise for `aOf`/`bOf`, so all three modes are left
--       with the same shape; see `Comp/ModelData.lean`'s `exists_forall_enabled_iff`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L102-L106
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L102-L106

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.pre1F_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (x : Finset (Fin d.nStates)) :
    d.toCsgQ.pre1F x = d.pre1Of hs x := by sorry
