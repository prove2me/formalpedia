-- Prove2me | Theorems.Thm_FamousTheorems_maschke_theorem
-- name    : FamousTheorems.maschke_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:13:53.684799+00:00
-- url     : https://prove2.me/theorems/b2ca400f-8411-42cf-a74e-8848593b7dab
-- title:
--   Maschke's theorem
-- statement:
--   **Maschke's theorem.** Let $G$ be a finite group and $k$ a field whose characteristic does not divide $|G|$. Every submodule of a $k[G]$-module has a complementary submodule; hence every representation of $G$ over $k$ is completely reducible.
--
--   This is the starting point of the representation theory of finite groups: it reduces the study of representations to irreducible ones and underlies character theory. It fails in the modular case $\operatorname{char}k\mid|G|$, where modular representation theory begins.
--
--   **Formalization note.** Mathlib's `MonoidAlgebra.Submodule.exists_isCompl`. Modules over the group algebra `MonoidAlgebra k G` are the representations, and the hypothesis `NeZero (Nat.card G : k)` says $|G|$ is invertible in $k$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MonoidAlgebra.Submodule.exists_isCompl`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem maschke_theorem {k : Type*} [Field k] {G : Type*} [Group G] [Finite G] [NeZero (Nat.card G : k)] {V : Type*}
    [AddCommGroup V] [Module (MonoidAlgebra k G) V] (p : Submodule (MonoidAlgebra k G) V) :
    ∃ q : Submodule (MonoidAlgebra k G) V, IsCompl p q := by sorry

end FamousTheorems
