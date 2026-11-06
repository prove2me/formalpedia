-- Prove2me | Theorems.Thm_Eight_ViaGrouping_keepsP_ofProcs
-- name    : Eight.ViaGrouping.keepsP_ofProcs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:30:57.225495+00:00
-- url     : https://prove2.me/theorems/ee2522ed-e061-4a4b-9b71-6f2b2abfe433
-- title:
--   Via Grouping: keeps P of Procs
-- statement:
--   The same, with P given in unary: what an algorithm for networks asks of its procedures
--   (`AlgKeeps`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Bridge.lean#L180-L181
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Bridge.lean#L180-L181

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

theorem Eight.ViaGrouping.keepsP_ofProcs {C : Type} [HasSize C] [Enc C] [Carried C] {Np : PNet C} {Pf : C → ℕ} {Q : Stepped (C × PsiQ) ℤ} (h : Np.Keeps) (hP : Unary Pf) (hQ : Nonempty (IsPolyT Q)) :
    KeepsP (ofProcs Np Pf Q) := by sorry
