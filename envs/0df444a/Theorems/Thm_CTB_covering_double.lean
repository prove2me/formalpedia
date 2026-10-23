-- Prove2me | Theorems.Thm_CTB_covering_double
-- name    : CTB.covering_double
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:11:59.995301+00:00
-- url     : https://prove2.me/theorems/51bac713-7b6f-41f5-8b08-b997cbd1aa53
-- title:
--   The regular coverings of the lattice corrections (Propositions 3.5 and 3.10)
-- statement:
--   The lattice corrections give regular coverings. For every n of at least four strings there is a pair of nested subgroups whose quotient is of order two, the smaller subgroup cut out by a character of the braid quotient on the larger one, surjective on the signs - the regular double covering of the G4 lattice correction; and a second pair of nested subgroups with the smaller subgroup cut out by three simultaneous characters, jointly surjective on the triples of signs - the regular eight-sheeted covering of the G6 lattice correction, with deck transformation group the order eight elementary two-group. These are Propositions 3.5 and 3.10 of the paper.
-- source:
--   O. Ocampo, Crystallographic quotients of Artin braid groups and torus bundles over flat 3-manifolds, arXiv:2610.20478 (2026), Section 3 (Propositions 3.5 and 3.10).

import Mathlib
import Definitions.Def_CTB_alg
import Definitions.Def_CTB_tor

namespace CTB

/-!  Milestone 6 (Propositions 3.5 and 3.10): the regular coverings of
the lattice corrections. For every n of at least four strings there is a
pair of nested subgroups whose quotient is of order two, given by a
character of the braid quotient with the smaller subgroup as its kernel
on the larger one - the regular double covering of the G4 lattice
correction; and there is a second pair of nested subgroups with the
smaller subgroup cut out by three simultaneous characters, jointly
surjective on triples of signs - the regular eight-sheeted covering of
the G6 lattice correction, with deck transformation group the order
eight elementary two-group. -/
theorem covering_double {n : ℕ} {Q : Type*} [Group Q]
    (W : CrystallographicBraidWorld n Q) (hn : 4 ≤ n) :
    (∃ (T1 T2 : Subgroup Q) (chi : Q →* Multiplicative (ZMod 2)),
        T1 ≤ T2 ∧
        (∀ g ∈ T2, ∀ k ∈ T1, g * k * g⁻¹ ∈ T1) ∧
        (∀ x ∈ T2, chi x = 1 ↔ x ∈ T1) ∧
        (∀ y : Multiplicative (ZMod 2), ∃ x ∈ T2, chi x = y)) ∧
    (∃ (T3 T4 : Subgroup Q) (chis : Fin 3 → (Q →* Multiplicative (ZMod 2))),
        T3 ≤ T4 ∧
        (∀ g ∈ T4, ∀ k ∈ T3, g * k * g⁻¹ ∈ T3) ∧
        (∀ x ∈ T4, (∀ j, chis j x = 1) ↔ x ∈ T3) ∧
        (∀ ys : Fin 3 → Multiplicative (ZMod 2), ∃ x ∈ T4, ∀ j, chis j x = ys j)) := by sorry

end CTB
