-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_nvio_incL
-- name    : ClauseBound.ParityChecks.BridgeInc.nvio_incL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:07.84445+00:00
-- url     : https://prove2.me/theorems/d49e28f3-2144-4b5a-b37a-b8da432699cd
-- title:
--   Bridge Inc: nvio inc L
-- statement:
--   The incidences of the checks before j and of check j that σ violates. (For j = r there is no
--   check j.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L179-L203
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L179-L203

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

theorem ClauseBound.ParityChecks.BridgeInc.nvio_incL {n r j : ℕ} {ψ : Fml} {Lam : List (List ℕ)} (h : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (hL : WfC ψ r Lam) (hj : j ≤ r) (σ : Fin (n + r) → Bool) :
    nvio (ext σ) (incL n ψ Lam j) = #(Dummy.inc (Vof (n := n) ψ) r (Lof ψ Lam) (J1 r j) (J2 r j) (xi σ) (yy σ)) := by sorry
