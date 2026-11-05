-- Prove2me | Theorems.Thm_Exits_stByAlgorithmOf
-- name    : Exits.stByAlgorithmOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:32:01.157989+00:00
-- url     : https://prove2.me/theorems/d1909696-db53-4f64-a831-c116d54e0352
-- title:
--   Exits: st By Algorithm Of
-- statement:
--   **Theorem 2 in its decision form by Algorithm 1**: «For every δ > 0 there is a deterministic
--   algorithm that computes the number of satisfying assignments of a 3-CNF on n variables, with any
--   number of clauses, in time O(2^{δn}).» Here in the deciding form. A Turing machine of Mathlib
--   simulates Sat(ℓ, τ), for the ℓ and τ that belong to δ/2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Decides.lean#L121-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Decides.lean#L121-L124

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_SecLevel_EStar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_Exits_Decides
set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Groundwork.Stepped Paper Eight Eight.SecNetworks Eight.ViaGrouping Suffices Enumerate

theorem Exits.stByAlgorithmOf : StByAlgorithmOf := by sorry
