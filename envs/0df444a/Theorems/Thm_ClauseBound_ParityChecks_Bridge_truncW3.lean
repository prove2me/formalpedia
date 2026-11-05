-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Bridge_truncW3
-- name    : ClauseBound.ParityChecks.Bridge.truncW3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:37:56.039589+00:00
-- url     : https://prove2.me/theorems/a70a2d20-1b86-4eee-8e67-99998b82fe8f
-- title:
--   Bridge: trunc W3
-- statement:
--   The sum over marks in three layers, written out.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Bridge.lean#L69-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Bridge.lean#L69-L73

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

theorem ClauseBound.ParityChecks.Bridge.truncW3 (N : ℕ) (w₀ w₁ w₂ : ℤ) (l₀ l₁ l₂ h₀ h₁ h₂ : ℕ) (L₀ L₁ L₂ : Fml) :
    truncW N [w₀, w₁, w₂] [l₀, l₁, l₂] [h₀, h₁, h₂] [L₀, L₁, L₂] = ∑ σ : Fin N → Bool,
      (∑ q ∈ Icc l₀ h₀, w₀ ^ q * ((nvio (PaddedDescent.F.Mark.ext σ) L₀).choose q : ℤ)) *
        ((∑ q ∈ Icc l₁ h₁, w₁ ^ q * ((nvio (PaddedDescent.F.Mark.ext σ) L₁).choose q : ℤ)) *
          ((∑ q ∈ Icc l₂ h₂, w₂ ^ q * ((nvio (PaddedDescent.F.Mark.ext σ) L₂).choose q : ℤ)) * 1)) := by sorry
