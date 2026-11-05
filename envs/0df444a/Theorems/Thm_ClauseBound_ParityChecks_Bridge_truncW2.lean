-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Bridge_truncW2
-- name    : ClauseBound.ParityChecks.Bridge.truncW2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:38:05.825203+00:00
-- url     : https://prove2.me/theorems/b042055a-7d19-4e6c-be77-ddbdb2b014e8
-- title:
--   Bridge: trunc W2
-- statement:
--   The sum over marks in two layers, written out.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Bridge.lean#L76-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Bridge.lean#L76-L79

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Definitions.Def_ClauseBound_ParityChecks_Bridge
set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Bridge
open Groundwork.Prog (Fml)
open PaddedDescent.F.Mark (nvio vio nSat)
open ClauseBound.TopN.EvalW (truncW)
open ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc

theorem ClauseBound.ParityChecks.Bridge.truncW2 (N : ℕ) (w₀ w₁ : ℤ) (l₀ l₁ h₀ h₁ : ℕ) (L₀ L₁ : Fml) :
    truncW N [w₀, w₁] [l₀, l₁] [h₀, h₁] [L₀, L₁] = ∑ σ : Fin N → Bool,
      (∑ q ∈ Icc l₀ h₀, w₀ ^ q * ((nvio (PaddedDescent.F.Mark.ext σ) L₀).choose q : ℤ)) *
        ((∑ q ∈ Icc l₁ h₁, w₁ ^ q * ((nvio (PaddedDescent.F.Mark.ext σ) L₁).choose q : ℤ)) * 1) := by sorry
