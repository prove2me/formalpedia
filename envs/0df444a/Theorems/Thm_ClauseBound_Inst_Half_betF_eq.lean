-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_betF_eq
-- name    : ClauseBound.Inst.Half.betF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:40:39.604805+00:00
-- url     : https://prove2.me/theorems/772e7249-a907-4ac5-8042-061a040916fd
-- title:
--   Half: bet F eq
-- statement:
--   The coefficient of the series of t_n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L89-L90
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L89-L90

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson

theorem ClauseBound.Inst.Half.betF_eq {W n : ℕ} (hn : n ≤ W) (r : ℤ) : betF W n r = bet n r := by sorry
