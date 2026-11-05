-- Prove2me | Theorems.Thm_CountKSat_ProgC_clause_of_G
-- name    : CountKSat.ProgC.clause_of_G
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:58:44.496796+00:00
-- url     : https://prove2.me/theorems/0053e375-d652-4a57-be6d-1c6c02b9faf4
-- title:
--   Prog C: clause of G
-- statement:
--   The clauses of the formula of a node have at most k literals, on variables below n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/ProgC.lean#L64-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/ProgC.lean#L64-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Mathlib.Tactic.Ring
import Definitions.Def_CountKSat_ProgC
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open CountKSat
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog
open CountKSat.ProgC
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}

theorem CountKSat.ProgC.clause_of_G (hI : Iface θ k D T q leafB Ok Node) {n : ℕ} {ψ : PFml} (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n)
    {s : PFml} {p t : ℕ} (hG : ProgMain.G Node ψ s p t) : ∀ C ∈ s, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := by sorry
