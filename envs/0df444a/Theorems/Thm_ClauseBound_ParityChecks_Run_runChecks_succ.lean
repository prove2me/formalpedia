-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Run_runChecks_succ
-- name    : ClauseBound.ParityChecks.Run.runChecks_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:40:29.896031+00:00
-- url     : https://prove2.me/theorems/52336376-56bc-4537-a5d9-ef93c8b019dc
-- title:
--   Run: run Checks succ
-- statement:
--   The Run construction uses the run Checks succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L321-L325
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L321-L325

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

theorem ClauseBound.ParityChecks.Run.runChecks_succ (j : ℕ) :
    q.runChecks orcA orcB (j + 1) = q.runChecks orcA orcB j ++ [q.runTo orcA orcB (q.runChecks orcA orcB j) q.m] := by sorry
