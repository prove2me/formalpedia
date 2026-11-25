-- Prove2me | Theorems.Thm_ErdosGirth_exists_params
-- name    : ErdosGirth.exists_params
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:29:03.763511+00:00
-- url     : https://prove2.me/theorems/8021a8e1-e5a6-5663-9bb3-d75ababb2e61
-- title:
--   Erdos Girth: exists params
-- statement:
--   The Erdos Girth construction uses the exists params property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L480-L519
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L480-L519

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth

theorem ErdosGirth.exists_params (g : ℕ) {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∃ (p : ℝ) (t : ℕ),
    0 ≤ p ∧ p ≤ 1 ∧ (t : ℝ) ≤ ε * n ∧
    2 / ((2 * n : ℕ) : ℝ) * ∑ ℓ ∈ range (g + 1), (((2 * n : ℕ) : ℝ) * p) ^ ℓ
      + ((2 * n).choose t : ℝ) * (1 - p) ^ t.choose 2 < 1 := by sorry
