-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Run_chkOK_mono
-- name    : ClauseBound.ParityChecks.Run.chkOK_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:56:22.265717+00:00
-- url     : https://prove2.me/theorems/d4be752f-e588-4707-b7a7-88a2de9a8415
-- title:
--   Run: chk OK mono
-- statement:
--   The Run construction uses the chk OK mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L54-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L54-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m)) (orcA : List Chk → ℤ) (orcB : List Chk → Chk → ℕ → ℕ → ℤ)
open ClauseBound.ParityChecks.Run

theorem ClauseBound.ParityChecks.Run.chkOK_mono {e e' : ℕ} (h : e ≤ e') {L : Chk} (hL : ChkOK e L) : ChkOK e' L := by sorry
