-- Prove2me | Theorems.Thm_FamousTheorems_jordan_holder
-- name    : FamousTheorems.jordan_holder
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:53.321604+00:00
-- url     : https://prove2.me/theorems/5a5f9086-2a9a-49f5-8819-54410d29256d
-- title:
--   The Jordan–Hölder theorem
-- statement:
--   **The Jordan–Hölder theorem.** Any two composition series with the same first and last terms are equivalent: they have the same length, and their successive factors agree up to a permutation and isomorphism.
--
--   For a finite group, the multiset of composition factors (simple groups) is therefore an invariant. The same holds for modules of finite length. It underlies the programme of classifying finite groups via finite simple groups and the notion of length in module theory.
--
--   **Formalization note.** Mathlib's `CompositionSeries.jordan_holder`, proved for a lattice with an abstract `JordanHolderLattice` structure (a notion of maximal step and of isomorphism of intervals satisfying the second isomorphism law). Subgroup and submodule lattices are the intended instances. `s₁.Equivalent s₂` means the series have the same length and some bijection of steps matches isomorphic factors.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CompositionSeries.jordan_holder`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem jordan_holder {X : Type*} [Lattice X] [JordanHolderLattice X] (s₁ s₂ : CompositionSeries X)
    (hb : RelSeries.head s₁ = RelSeries.head s₂) (ht : RelSeries.last s₁ = RelSeries.last s₂) :
    s₁.Equivalent s₂ := by sorry

end FamousTheorems
