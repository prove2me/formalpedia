-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Ev_stEvW
-- name    : ClauseBound.ParityChecks.Ev.stEvW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:37:41.540199+00:00
-- url     : https://prove2.me/theorems/a022507d-fd50-4c52-87df-e97607ec6c5a
-- title:
--   Ev: st Ev W
-- statement:
--   One evaluation is exact on three layers (or two) of clauses of 1 to k + 1 literals on n + r
--   variables in which no variable occurs too often.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Ev.lean#L82-L90
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Ev.lean#L82-L90

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Ev
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Ev
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW

theorem ClauseBound.ParityChecks.Ev.stEvW (hV : StMarkVal) (hP : StProfSum) (hPr : StMarkPresents) (hSz : StMarkSized) (hVal : StValS) : StEvW := by sorry
