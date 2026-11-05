-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_HalfTabKF_padKF_mono
-- name    : ClauseBound.Inst.Half.HalfTabKF.padKF_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:44:34.93704+00:00
-- url     : https://prove2.me/theorems/e012e901-6f40-4958-a583-2e01bb382a03
-- title:
--   Half Tab KF: pad KF mono
-- statement:
--   `padKF` grows with the sum and with the number of parts.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabKF.lean#L41-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabKF.lean#L41-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Definitions.Def_ClauseBound_Boson_KF
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Inst_HalfTabKF
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
open ClauseBound.Inst.Half.HalfTabKF

theorem ClauseBound.Inst.Half.HalfTabKF.padKF_mono (W Δ h : ℕ) {s s' L L' : ℕ} (hs : s ≤ s') (hL : L ≤ L') : padKF W Δ h s L ≤ padKF W Δ h s' L' := by sorry
