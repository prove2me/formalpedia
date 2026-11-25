-- Prove2me | Theorems.Thm_ErdosGirth_expected_cyc_le
-- name    : ErdosGirth.expected_cyc_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:28:23.459739+00:00
-- url     : https://prove2.me/theorems/9fcbb12e-b95d-4ae7-84c5-36ae320ce586
-- title:
--   Erdos Girth: expected cyc le
-- statement:
--   The Erdos Girth construction uses the expected cyc le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L170-L189
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L170-L189

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
open Classical

theorem ErdosGirth.expected_cyc_le {m : ℕ} (g : ℕ) {p : ℝ} (hp0 : 0 ≤ p) :
    ∑ S ∈ (pairs m).powerset, wt m p S * ∑ u, cyc m g S u
      ≤ ∑ ℓ ∈ range (g + 1), ((m : ℝ) * p) ^ ℓ := by sorry
