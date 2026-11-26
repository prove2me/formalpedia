-- Prove2me | Theorems.Thm_Erdos338_erdos_338_variants_lowerDensity_pos
-- name    : Erdos338.erdos_338.variants.lowerDensity_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:01:28.655431+00:00
-- url     : https://prove2.me/theorems/e7d1fd0f-bb82-5b88-867b-a553d8189d08
-- title:
--   variants: lower Density pos
-- statement:
--   If $A \setminus F$ is a basis for every finite set $F$ and $A$ has positive lower density, then $A$
--   has a restricted order: every sufficiently large integer is a sum of a bounded number of distinct
--   elements of $A$.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Solution.lean#L89-L109
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Solution.lean#L89-L109

module
public import Mathlib
public import Definitions.Def_Erdos338
public import Definitions.Def_Erdos338_Solution
set_option autoImplicit true
@[expose] public section
public section
open Filter
open scoped Topology
open Erdos338

theorem Erdos338.erdos_338.variants.lowerDensity_pos :
    ∀ A : Set ℕ, (∀ F : Set ℕ, F.Finite → ∃ h, HasOrder (A \ F) h) → 0 < A.lowerDensity →
      ∃ t, HasRestrictedOrder A t := by sorry
