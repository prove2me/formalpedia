-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_vio_ext
-- name    : ClauseBound.ParityChecks.BridgeInc.vio_ext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:37:33.233191+00:00
-- url     : https://prove2.me/theorems/1925d927-b6b8-4bd1-b626-20e6ecfdc9d3
-- title:
--   Bridge Inc: vio ext
-- statement:
--   A clause in the variables of ψ sees only ξ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L76-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L76-L79

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

theorem ClauseBound.ParityChecks.BridgeInc.vio_ext {n r : ℕ} (σ : Fin (n + r) → Bool) {C : Cl} (h : ∀ l ∈ C, l.1 < n) : vio (ext σ) C = vio (ext (xi σ)) C := by sorry
