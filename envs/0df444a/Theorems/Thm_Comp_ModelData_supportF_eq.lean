-- Prove2me | Theorems.Thm_Comp_ModelData_supportF_eq
-- name    : Comp.ModelData.supportF_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:38:20.397084+00:00
-- url     : https://prove2.me/theorems/dd1d3bf3-39ec-4356-9c73-492e24ab12da
-- title:
--   Model Data: support F eq
-- statement:
--   **The bridge, and the quarantine.** `Comp/QualitativeFinset.lean`'s `supportF` -- a filter over
--       every state, with a rational disequality in it -- is the padded transition's own key set.
--
--       Computing a support costs the row's length instead of the state count; and nothing above this
--       line touches a weight at all, since `supportOf` is built from `keysNat`, which is `ℕ` data. So
--       the kernel reduces every operator above it even when the weights are fractions it could not so
--       much as evaluate. That is the job `Comp/HideOrRunQ.lean` and `Comp/SafetyChainQ.lean` each do by
--       hand for their own game, except that those tables rely on their kernels being `0`/`1`; this one
--       holds for any model, and the three `ℚ` conditions it rests on are proved once per model rather
--       than reproved inside every fixed-point check.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L764-L772
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L764-L772

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.supportF_eq (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (hs : d.Shape) (hnn : d.Nonneg) (hnz : d.Nonzero) (s : Fin d.nStates) (a1 : Fin d.nAct1)
    (a2 : Fin d.nAct2) :
    d.toCsgQ.supportF s a1 a2 = d.supportOf hs s a1 a2 := by sorry
