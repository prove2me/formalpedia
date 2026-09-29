-- Prove2me | Theorems.Thm_AdicCompletion_finite_residueField_and_card_eq_of_isMaximal
-- name    : AdicCompletion.finite_residueField_and_card_eq_of_isMaximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/068d3b2f-7c08-578c-816e-ffe926242aae
-- title:
--   Residue field of an adic completion at a maximal ideal
-- statement:
--   Let $S$ be a commutative Noetherian ring and let $x \subseteq S$ be a maximal ideal whose residue ring $S/x$ is finite, and suppose given a local-ring structure `inst` on the $x$-adic completion `AdicCompletion x S` (this structure is taken as an explicit argument rather than inferred, and the residue field is formed with respect to it). Then two things hold: the residue field of `AdicCompletion x S` for the structure `inst` is finite, and its cardinality, measured by `Nat.card`, equals the cardinality of $S/x$. No identification of the residue field with $S/x$ is recorded in the statement; only finiteness and equality of cardinalities are asserted.
--
--   This is the standard fact that completing a Noetherian ring at a maximal ideal does not change the residue field, so that finiteness of $S/x$ passes to the completion. It is used in the comparison of an adic completion with a tensor product under flatness hypotheses, where the cardinality of the residue field is one of the matching conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_finite_residueField_and_card_eq_of_isMaximal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AdicCompletion.finite_residueField_and_card_eq_of_isMaximal
    (S : Type) [CommRing S] [IsNoetherianRing S] (x : Ideal S) [x.IsMaximal] [Finite (S ⧸ x)]
    (inst : IsLocalRing (AdicCompletion x S)) :
    Finite (@IsLocalRing.ResidueField (AdicCompletion x S) _ inst) ∧
      Nat.card (@IsLocalRing.ResidueField (AdicCompletion x S) _ inst) = Nat.card (S ⧸ x) := by sorry
