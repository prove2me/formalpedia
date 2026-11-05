-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Run_Inv_lt_one
-- name    : ClauseBound.ParityChecks.Run.Inv.lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:04:53.996308+00:00
-- url     : https://prove2.me/theorems/ffe6998f-5255-4550-bad7-f83835acd7de
-- title:
--   Inv: lt one
-- statement:
--   In a state that the run has reached the potential is below 1 (the proof gives below 3/4).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L247-L257
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L247-L257

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

theorem ClauseBound.ParityChecks.Run.Inv.lt_one (hq : Hyp q (Fintype.card X) ε) {Ls : List Chk} {cur : Chk} {e : ℕ} (h : Inv q V ε Ls cur e) : UU q V Ls cur e < 1 := by sorry
