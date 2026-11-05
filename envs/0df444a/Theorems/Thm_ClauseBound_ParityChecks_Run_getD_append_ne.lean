-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Run_getD_append_ne
-- name    : ClauseBound.ParityChecks.Run.getD_append_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:46:07.228575+00:00
-- url     : https://prove2.me/theorems/872f4877-8df7-420e-94cc-4f36be723f29
-- title:
--   Run: get D append ne
-- statement:
--   The Run construction uses the get D append ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L49-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L49-L52

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

theorem ClauseBound.ParityChecks.Run.getD_append_ne (Ls : List Chk) (c : Chk) {j : ℕ} (hj : j ≠ Ls.length) : (Ls ++ [c]).getD j [] = Ls.getD j [] := by sorry
