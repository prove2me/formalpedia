-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_HalfTabKF_kfInit_eq
-- name    : ClauseBound.Inst.Half.HalfTabKF.kfInit_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:40:34.084071+00:00
-- url     : https://prove2.me/theorems/e9bed28c-98a4-4616-9058-5dd28df2b453
-- title:
--   Half Tab KF: kf Init eq
-- statement:
--   The tables at the start, as tables of functions.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabKF.lean#L67-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabKF.lean#L67-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Definitions.Def_ClauseBound_Boson_KF
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
open ClauseBound.Inst.Half.HalfTabKF

theorem ClauseBound.Inst.Half.HalfTabKF.kfInit_eq (h : ℕ) (flat : List (List ℕ)) :
    kfInit h flat = (List.range (h + 1)).map fun w => tab flat fun π σ => if w = 0 then (if π = σ then 1 else 0) else 0 := by sorry
