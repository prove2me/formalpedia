-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Run_bd_of_lt_one
-- name    : ClauseBound.ParityChecks.Run.bd_of_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:04:56.180862+00:00
-- url     : https://prove2.me/theorems/bb93cf09-47f7-4cbb-9b52-c7d132f1d7dc
-- title:
--   Run: bd of lt one
-- statement:
--   A potential below 1 gives the three bounds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L198-L203
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L198-L203

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

theorem ClauseBound.ParityChecks.Run.bd_of_lt_one (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) {Ls : List Chk} {cur : Chk} {e : ℕ} (hj : Ls.length < q.r) (hc : ChkOK e cur)
    (hU : UU q V Ls cur e < 1) : Bd q (lam q.m (Ls ++ [cur])) := by sorry
