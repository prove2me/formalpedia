-- Prove2me | Theorems.Thm_CliqueMinors_eq_of_card_le_three
-- name    : CliqueMinors.eq_of_card_le_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:33:40.198748+00:00
-- url     : https://prove2.me/theorems/3a1ad3fe-c977-4aab-83bd-ca8a333b6869
-- title:
--   Clique Minors: eq of card le three
-- statement:
--   The Clique Minors construction uses the eq of card le three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L207-L219
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L207-L219

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

theorem CliqueMinors.eq_of_card_le_three {s : Finset V} (h : s.card ≤ 3) {p q r : V} (hp : p ∈ s)
    (hq : q ∈ s) (hr : r ∈ s) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) {t : V} (ht : t ∈ s) :
    t = p ∨ t = q ∨ t = r := by sorry
