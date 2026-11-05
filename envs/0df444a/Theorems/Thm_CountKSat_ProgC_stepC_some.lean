-- Prove2me | Theorems.Thm_CountKSat_ProgC_stepC_some
-- name    : CountKSat.ProgC.stepC_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:58:18.934992+00:00
-- url     : https://prove2.me/theorems/6e73e494-74b8-44e0-ad8e-c4d80f7984b2
-- title:
--   Prog C: step C some
-- statement:
--   The two children of a step of the counting tree, written out.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/ProgC.lean#L89-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/ProgC.lean#L89-L93

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
set_option autoImplicit false
section
section
open CountKSat
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog
open CountKSat.ProgC
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}

theorem CountKSat.ProgC.stepC_some {x l h : CNode} (hst : stepC θ k x = some (l, h)) :
    ∃ H P, pickK θ k x.1 = some (H, P) ∧ l = (addP [H] x.1, x.2) ∧ h = (addP P x.1, negU H ++ x.2) := by sorry
