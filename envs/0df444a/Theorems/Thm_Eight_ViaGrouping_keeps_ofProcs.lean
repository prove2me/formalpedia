-- Prove2me | Theorems.Thm_Eight_ViaGrouping_keeps_ofProcs
-- name    : Eight.ViaGrouping.keeps_ofProcs
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:04:39.364729+00:00
-- url     : https://prove2.me/theorems/9f588630-f75e-4a45-8f63-ea6f353ab477
-- title:
--   Via Grouping: keeps of Procs
-- statement:
--   The procedures `ofProcs Np Pf Q` have polynomial-time steps (and give P_a and c_{a,b} in unary)
--   if those of proof/networks/Paper have and Q has.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Bridge.lean#L173-L176
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Bridge.lean#L173-L176

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Bridge
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Finset Stepped Eight.SecNetworks
variable {g : ℕ}

theorem Eight.ViaGrouping.keeps_ofProcs {C : Type} [HasSize C] [Enc C] [Carried C] {Np : PNet C} (Pf : C → ℕ) {Q : Stepped (C × PsiQ) ℤ} (h : Np.Keeps) (hQ : Nonempty (IsPolyT Q)) :
    (ofProcs Np Pf Q).Keeps := by sorry
