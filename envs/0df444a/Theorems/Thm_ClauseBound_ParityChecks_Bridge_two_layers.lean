-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Bridge_two_layers
-- name    : ClauseBound.ParityChecks.Bridge.two_layers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:51:07.019987+00:00
-- url     : https://prove2.me/theorems/84688549-683d-47f9-ad99-c5fef3e1f4c7
-- title:
--   Bridge: two layers
-- statement:
--   A sum over marks in two layers, the second one the incidences of the complete checks before j,
--   is 2^r·Σ_ξ f(ξ)·∏_{j' < j} [|V_j'(ξ)| even] modulo 2^{M+1}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Bridge.lean#L107-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Bridge.lean#L107-L124

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

theorem ClauseBound.ParityChecks.Bridge.two_layers {n r j : ℕ} {ψ : Fml} {Lam : List (List ℕ)} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (hW : WfC ψ r Lam) (hj : j ≤ r) (M : ℕ)
    (w : ℤ) (l h : ℕ) (f : (Fin n → Bool) → ℤ) (hf : ∀ ξ, ∑ q ∈ Icc l h, w ^ q * ((#(Vof ψ ξ)).choose q : ℤ) = f ξ) :
    truncW (n + r) [w, -2] [l, 0] [h, M] [ψ, incL n ψ (Lam.take j) j] ≡
      2 ^ r * ∑ ξ, f ξ * ∏ j' ∈ range j, ev #(Lof ψ Lam j' ∩ Vof ψ ξ) [ZMOD 2 ^ (M + 1)] := by sorry
