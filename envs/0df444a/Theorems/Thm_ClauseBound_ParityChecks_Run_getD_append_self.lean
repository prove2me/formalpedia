-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Run_getD_append_self
-- name    : ClauseBound.ParityChecks.Run.getD_append_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:04:39.877279+00:00
-- url     : https://prove2.me/theorems/51a41640-3d4d-4d66-bb3f-4bf1c6e02e5c
-- title:
--   Run: get D append self
-- statement:
--   The Run construction uses the get D append self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L46-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L46-L47

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

theorem ClauseBound.ParityChecks.Run.getD_append_self (Ls : List Chk) (c : Chk) : (Ls ++ [c]).getD Ls.length [] = c := by sorry
