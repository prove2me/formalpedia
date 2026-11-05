-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Structure_structure_
-- name    : ClauseBound.ParityChecks.Structure.structure_
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:59:41.654204+00:00
-- url     : https://prove2.me/theorems/28573072-8e8c-457b-be6f-afd6affa95a0
-- title:
--   Structure: structure
-- statement:
--   What Υ < 1 gives in any state: fewer than 8pmr pairs, 2^|Λ_j'| < 8r(1 + p)^m for every check,
--   and 2^load(e) < 8m(1 + p)^r for every clause e, where load(e) is the number of checks j' < r that
--   contain e.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Structure.lean#L51-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Structure.lean#L51-L76

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_ClauseBound_ParityChecks_Structure
set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Structure
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]

theorem ClauseBound.ParityChecks.Structure.structure_ (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) (D : Finset E)
    (hnn : 0 ≤ Upar V nb r j Λ D ∧ 0 ≤ Uinc nb r j Λ D ∧ 0 ≤ Urow nb r j Λ D ∧ 0 ≤ Ucol nb r j Λ D)
    (hnb : 2 ≤ nb) (hE : 1 ≤ Fintype.card E) (hs : IsState r j Λ D) (hU : Ups V nb r j Λ D < 1) :
    ((∑ j' ∈ range r, #(Λ j') : ℕ) : ℚ) < 8 * pr nb * Fintype.card E * r ∧
    (∀ j' < r, (2 : ℚ) ^ #(Λ j') < 8 * r * (1 + pr nb) ^ Fintype.card E) ∧
    ∀ e : E, (2 : ℚ) ^ #{j' ∈ range r | e ∈ Λ j'} < 8 * Fintype.card E * (1 + pr nb) ^ r := by sorry
