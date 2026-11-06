-- Prove2me | Theorems.Thm_Complement_entry_compl
-- name    : Complement.entry_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:23:49.505869+00:00
-- url     : https://prove2.me/theorems/89227e45-1d99-4fdb-93a3-296122b87b7a
-- title:
--   Complement: entry compl
-- statement:
--   One entry: u ≠ v and the entry (u, v) of the matrix of G is 0, exactly if u and v are adjacent
--   in the complement graph.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Complement/Sets.lean#L69-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Complement/Sets.lean#L69-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Complement_Defs
import Definitions.Def_GraphProblems_Read
import Mathlib.Tactic
import Definitions.Def_Complement_Sets
set_option autoImplicit false
section
section
open Complement
open Groundwork Groundwork.Prog CountKSat GraphProblems

theorem Complement.entry_compl {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) (inst : Decidable (Gᶜ.Adj u v)) :
    (u.val != v.val && !adjB n (matrix G) u.val v.val) = @decide (Gᶜ.Adj u v) inst := by sorry
