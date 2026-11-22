-- Prove2me | Theorems.Thm_Comp_ModelData_supportOf_padFin1
-- name    : Comp.ModelData.supportOf_padFin1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:44:58.770067+00:00
-- url     : https://prove2.me/theorems/64828c90-9462-407a-8148-b4671f1d3f5b
-- title:
--   Model Data: support Of pad Fin1
-- statement:
--   The support does not see a row action's padding. Stated with `padFin1` on the left so that it
--       rewrites in the direction the operator proofs need.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L741-L745
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L741-L745

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.supportOf_padFin1 (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) :
    d.supportOf hs s (d.padFin1 hs s a1) a2 = d.supportOf hs s a1 a2 := by sorry
