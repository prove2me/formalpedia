-- Prove2me | Theorems.Thm_Comp_ModelData_lpre1Tr_eq
-- name    : Comp.ModelData.lpre1Tr_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:24:25.114751+00:00
-- url     : https://prove2.me/theorems/2d39d403-8b00-48a7-923b-28645106d4ff
-- title:
--   Model Data: lpre1 Tr eq
-- statement:
--   **`Lpre1`, narrowed.** The witness family is given twice -- the dense one the specification
--       talks about and the narrow one the computation carries -- related by `∩ enabled1` at every
--       state. The dense family must be pad-saturated, which `padSat1_lStepF_iterate` supplies for the
--       family that actually arises.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L455-L462
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L455-L462

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.lpre1Tr_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (wF wTr : Fin d.nStates → Finset (Fin d.nAct1))
    (hw : ∀ s, wTr s = wF s ∩ d.enabled1 hs s) (hpad : ∀ s, d.PadSat1 hs s (wF s))
    (x : Finset (Fin d.nStates)) :
    d.lpre1Tr hs wTr x = d.toCsgQ.lpre1F wF x := by sorry
