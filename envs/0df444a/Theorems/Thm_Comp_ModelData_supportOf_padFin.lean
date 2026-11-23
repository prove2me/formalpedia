-- Prove2me | Theorems.Thm_Comp_ModelData_supportOf_padFin
-- name    : Comp.ModelData.supportOf_padFin
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:23:55.060827+00:00
-- url     : https://prove2.me/theorems/4620b366-070c-4a72-a535-65991c01b031
-- title:
--   Model Data: support Of pad Fin
-- statement:
--   The support is padding-invariant -- the statement the quantifier swap consumes.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L734-L738
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L734-L738

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.supportOf_padFin (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) :
    d.supportOf hs s (d.padFin1 hs s a1) (d.padFin2 hs s a2) = d.supportOf hs s a1 a2 := by sorry
