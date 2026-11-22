-- Prove2me | Theorems.Thm_Comp_ModelData_bF_eq_univ_iff
-- name    : Comp.ModelData.bF_eq_univ_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:46:19.171295+00:00
-- url     : https://prove2.me/theorems/31bfc7e7-f09c-41bd-9aec-79c20797d2e1
-- title:
--   Model Data: b F eq univ iff
-- statement:
--   **The test the operators actually consume.** `apre1Of` and `lpre1Of` ask whether every column
--       action is answered; over transitions that becomes whether every *enabled* one is. The two agree
--       because `bF`'s output is pad-saturated, so a disabled column action is in it exactly when its
--       representative is.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L329-L344
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L329-L344

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.bF_eq_univ_iff [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (s : Fin d.nStates) (v1 : Finset (Fin d.nAct1))
    (x : Finset (Fin d.nStates)) :
    d.toCsgQ.bF v1 x s = Finset.univ ↔ d.bTr hs v1 x s = d.enabled2 hs s := by sorry
