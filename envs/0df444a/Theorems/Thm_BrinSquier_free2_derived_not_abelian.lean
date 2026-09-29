-- Prove2me | Theorems.Thm_BrinSquier_free2_derived_not_abelian
-- name    : BrinSquier.free2_derived_not_abelian
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-13T07:03:04.631354+00:00
-- url     : https://prove2.me/theorems/01061fc2-d389-42f8-80c7-d5334b856e6e
-- title:
--   The derived subgroup of a free group of rank two is not abelian
-- statement:
--   The commutator subgroup of the free group on two generators contains two elements that do not commute. Equivalently, $F_2$ is not metabelian.
--
--   Writing $a, b$ for the two free generators, the witnesses are the commutators
--
--   $$u = a b a^{-1} b^{-1}, \qquad v = a b^{2} a^{-1} b^{-2},$$
--
--   both of which lie in the derived subgroup by construction.
--
--   **Role.** Brin-Squier derive their Theorem (3.1) from the dichotomy (3.2) by remarking that a free group of rank greater than one is neither metabelian nor contains a free abelian subgroup of infinite rank. This statement is the first half of that remark, in the form the rank-two route needs: applying the dichotomy to the derived subgroup of a free group of rank two yields either an abelian derived subgroup or a copy of $\mathbb{Z}^2$, and it is this statement that closes the first horn.
--
--   **Formalization note.** The claim is an existential about two specific elements; it produces no subgroup object, and says nothing about which elements fail to commute beyond exhibiting a pair.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 494, in the proof of Theorem (3.1): "A free group of rank greater than 1 is neither metabelian nor does it contain a free abelian group of infinite rank." The paper asserts this without proof. PROVENANCE: the statement formalized here is the non-metabelian half of that remark, specialized to rank two, which is what the rank-two form of (3.2) consumes.

import Mathlib

namespace BrinSquier

theorem free2_derived_not_abelian :
    ∃ u v : FreeGroup (Fin 2), u ∈ commutator (FreeGroup (Fin 2)) ∧
      v ∈ commutator (FreeGroup (Fin 2)) ∧ u * v ≠ v * u := by
  sorry

end BrinSquier
