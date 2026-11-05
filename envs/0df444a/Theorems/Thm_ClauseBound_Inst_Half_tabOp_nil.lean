-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_tabOp_nil
-- name    : ClauseBound.Inst.Half.tabOp_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:42:15.032881+00:00
-- url     : https://prove2.me/theorems/c207c71f-d83b-4aee-95e6-712bd67abfda
-- title:
--   Half: tab Op nil
-- statement:
--   The Half construction uses the tab Op nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L130-L130
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L130-L130

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

theorem ClauseBound.Inst.Half.tabOp_nil (pad : U) (W : ℕ) (flat : List (List ℕ)) : tabOp pad W flat [] = cap pad [] (oneT flat) := by sorry
