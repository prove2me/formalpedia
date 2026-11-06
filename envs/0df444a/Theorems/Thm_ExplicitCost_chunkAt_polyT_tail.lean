-- Prove2me | Theorems.Thm_ExplicitCost_chunkAt_polyT_tail
-- name    : ExplicitCost.chunkAt_polyT_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:57:59.22709+00:00
-- url     : https://prove2.me/theorems/ab97093e-c7e3-4ae1-b12e-01d6e10b6e70
-- title:
--   Explicit Cost: chunk At poly T tail
-- statement:
--   A chunk of a word, for lengths that are constant from a place given in unary on; the number of
--   the chunk may be given in binary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyLists.lean#L120-L126
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyLists.lean#L120-L126

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_GridProcedures
import Definitions.Def_ClauseBound_Alg_CertGridG
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyLists
set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG
variable {α : Type} [Enc α]

theorem ExplicitCost.chunkAt_polyT_tail {n : α → ℕ → ℕ} {m κ : α → ℕ} {w : α → List Bool} (hn : PolyT fun p : α × ℕ => n p.1 p.2) (hm : Unary m) (hκ : PolyT κ) (hw : PolyT w)
    (h : ∀ x k, m x ≤ k → n x k = n x (m x)) : PolyT fun x => chunkAt (n x) (κ x) (w x) := by sorry
