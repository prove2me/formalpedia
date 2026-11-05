-- Prove2me | Theorems.Thm_Exits_stProofNamedOf
-- name    : Exits.stProofNamedOf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:29:50.976692+00:00
-- url     : https://prove2.me/theorems/47e822bf-381d-4ded-a94c-d49be8fbfe29
-- title:
--   Exits: st Proof Named Of
-- statement:
--   **The proof of Theorem 2 in Section 6, for a named machine**: «Fix such a K ≥ 72/δ' and put g =
--   3K⁸ … By Lemma 4 with ε = δ/3, … it suffices to compute the number of satisfying assignments of a
--   3-CNF Φ on n variables with m ≤ Mn clauses, in time O(2^{δ'm}) plus a polynomial in n.» From «it
--   suffices», read for deciding, Lemma 1 for the algorithm of its proof, and its polynomial-time steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Decides.lean#L74-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Decides.lean#L74-L83

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

theorem Exits.stProofNamedOf : StProofNamedOf := by sorry
