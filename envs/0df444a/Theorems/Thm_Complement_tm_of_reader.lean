-- Prove2me | Theorems.Thm_Complement_tm_of_reader
-- name    : Complement.tm_of_reader
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:24:13.122128+00:00
-- url     : https://prove2.me/theorems/88cf4db6-e21a-4dd5-ae6c-714447bd1d2f
-- title:
--   Complement: tm of reader
-- statement:
--   From a machine cut into steps on the words `codeWith G s` to a Turing machine: if Ms has
--   polynomial-time steps and returns f(G, s), for s ≤ n, within c·2^{(δ/2)n} steps on states of size at
--   most c·(n + n² + 2)^c, and `post` is polynomial time, then a Turing machine with finite alphabets
--   halts on `codeWith G s` with `post (f(G, s))` within ⌊C·2^{δn}⌋ steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Complement/Main.lean#L38-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Complement/Main.lean#L38-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Complement_Defs
import Definitions.Def_Complement_Readers
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Host
import Definitions.Def_ToTuring_Poly_Basic
import Mathlib.Tactic
import Definitions.Def_Complement_Main
set_option autoImplicit false
section
section
open Complement
open Groundwork Groundwork.Prog CountKSat GraphProblems Turing

theorem Complement.tm_of_reader (Ms : Stepped (List Bool) ℕ) (hp : Nonempty (IsPolyT Ms)) (f : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ) (c : ℕ)
    (h : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n → ∃ T : ℕ, Ms.Runs (codeWith G s) T (c * (n + n * n + 2) ^ c) (f n G s) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ / 2 * n))
    (post : ℕ → List Bool) (hpost : PolyT post) :
    ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n →
      Outputs M (codeWith G s) (post (f n G s)) ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by sorry
