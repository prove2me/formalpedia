-- Prove2me | Theorems.Thm_CliqueMinors_three_le_card
-- name    : CliqueMinors.three_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:33:28.923536+00:00
-- url     : https://prove2.me/theorems/b1a6e17e-ad65-5575-94b2-5e32d0f3526c
-- title:
--   Clique Minors: three le card
-- statement:
--   The Clique Minors construction uses the three le card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L189-L195
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L189-L195

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]
omit [Fintype V]

theorem CliqueMinors.three_le_card {s : Finset V} {p q r : V} (hp : p ∈ s) (hq : q ∈ s) (hr : r ∈ s)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : 3 ≤ s.card := by sorry
