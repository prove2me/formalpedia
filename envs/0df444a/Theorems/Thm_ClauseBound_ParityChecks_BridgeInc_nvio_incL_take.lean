-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_nvio_incL_take
-- name    : ClauseBound.ParityChecks.BridgeInc.nvio_incL_take
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:37:10.87291+00:00
-- url     : https://prove2.me/theorems/fa1c8fb4-87e3-4bf0-ba83-1e6707090b78
-- title:
--   Bridge Inc: nvio inc L take
-- statement:
--   The incidences of the checks before j that σ violates.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L217-L223
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L217-L223

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

theorem ClauseBound.ParityChecks.BridgeInc.nvio_incL_take {n r j : ℕ} {ψ : Fml} {Lam : List (List ℕ)} (h : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (hL : WfC ψ r Lam) (hj : j ≤ r) (σ : Fin (n + r) → Bool) :
    nvio (ext σ) (incL n ψ (Lam.take j) j) = #(Dummy.inc (Vof (n := n) ψ) r (Lof ψ Lam) (J1 r j) ∅ (xi σ) (yy σ)) := by sorry
