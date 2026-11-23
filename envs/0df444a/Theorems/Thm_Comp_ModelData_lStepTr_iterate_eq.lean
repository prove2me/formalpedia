-- Prove2me | Theorems.Thm_Comp_ModelData_lStepTr_iterate_eq
-- name    : Comp.ModelData.lStepTr_iterate_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:24:15.826664+00:00
-- url     : https://prove2.me/theorems/651c2656-674a-4718-91e0-8735f542127e
-- title:
--   Model Data: l Step Tr iterate eq
-- statement:
--   **The two inner climbs correspond, stage by stage.** One step of the chain: `bTr` drops the
--       disabled rows (`bTr_inter_enabled1`, on the dense stage's pad-saturation), `aTr` ignores the
--       disabled columns it is handed (`aTr_inter_enabled2`), and `aTr_eq` then identifies the result
--       with the dense step restricted -- its pad-saturation hypothesis discharged by `padSat2_bF`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L398-L411
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L398-L411

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.lStepTr_iterate_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) (k : ℕ) :
    (d.lStepTr hs x y s)^[k] ∅
      = (d.toCsgQ.lStepF x y s)^[k] ∅ ∩ d.enabled1 hs s := by sorry
