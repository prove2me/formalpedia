-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_HalfTabKF_getD_map_range
-- name    : ClauseBound.Inst.Half.HalfTabKF.getD_map_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:40:15.12694+00:00
-- url     : https://prove2.me/theorems/4fbd1c06-ee1d-4a1b-bc0b-150a8b438b86
-- title:
--   Half Tab KF: get D map range
-- statement:
--   The member number w of a list made from 0, …, h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabKF.lean#L37-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabKF.lean#L37-L38

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

theorem ClauseBound.Inst.Half.HalfTabKF.getD_map_range {h w : ℕ} (hw : w ≤ h) (f : ℕ → List ℤ) : ((List.range (h + 1)).map f).getD w [] = f w := by sorry
