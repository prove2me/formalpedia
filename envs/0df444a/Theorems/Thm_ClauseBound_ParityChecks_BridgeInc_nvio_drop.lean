-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_nvio_drop
-- name    : ClauseBound.ParityChecks.BridgeInc.nvio_drop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:50:19.677513+00:00
-- url     : https://prove2.me/theorems/9b7157cc-cf5e-4559-ae1e-96833e982505
-- title:
--   Bridge Inc: nvio drop
-- statement:
--   The clauses from number t on that σ violates.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L99-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L99-L102

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

theorem ClauseBound.ParityChecks.BridgeInc.nvio_drop {n r : ℕ} {ψ : Fml} (h : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (t : ℕ) (σ : Fin (n + r) → Bool) :
    nvio (ext σ) (ψ.drop t) = #(Dof ψ t ∩ Vof ψ (xi σ)) := by sorry
