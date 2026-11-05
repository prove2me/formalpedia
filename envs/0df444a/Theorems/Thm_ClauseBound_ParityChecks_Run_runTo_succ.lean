-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Run_runTo_succ
-- name    : ClauseBound.ParityChecks.Run.runTo_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:46:08.130624+00:00
-- url     : https://prove2.me/theorems/ce363902-708a-4320-a6a5-105c48e0f2e1
-- title:
--   Run: run To succ
-- statement:
--   The Run construction uses the run To succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L316-L319
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L316-L319

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
variable {q}
variable {V} {orcA orcB} {ε : ℚ}

theorem ClauseBound.ParityChecks.Run.runTo_succ (Ls : List Chk) (e : ℕ) : q.runTo orcA orcB Ls (e + 1) = q.decide1 orcA orcB Ls (q.runTo orcA orcB Ls e) e := by sorry
