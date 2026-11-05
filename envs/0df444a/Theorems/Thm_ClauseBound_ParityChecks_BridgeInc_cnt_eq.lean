-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_cnt_eq
-- name    : ClauseBound.ParityChecks.BridgeInc.cnt_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:50:39.493279+00:00
-- url     : https://prove2.me/theorems/85be123f-79a3-4675-bb1e-2d158fd88436
-- title:
--   Bridge Inc: cnt eq
-- statement:
--   The number of clauses of check j that σ violates, as the number of elements of a set.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L148-L152
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L148-L152

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_NetDefs
import Definitions.Def_ClauseBound_ParityChecks_Dummy
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
set_option autoImplicit false
section
section
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc

theorem ClauseBound.ParityChecks.BridgeInc.cnt_eq {n r : ℕ} (σ : Fin (n + r) → Bool) {ψ : Fml} (h : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) {r' : ℕ} {Lam : List (List ℕ)} (hL : WfC ψ r' Lam) (j : ℕ) :
    cnt (ext σ) ψ Lam j = #(Lof ψ Lam j ∩ Vof ψ (xi σ)) := by sorry
