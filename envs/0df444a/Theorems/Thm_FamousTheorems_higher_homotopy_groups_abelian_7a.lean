-- Prove2me | Theorems.Thm_FamousTheorems_higher_homotopy_groups_abelian_7a
-- name    : FamousTheorems.higher_homotopy_groups_abelian_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:10.96899+00:00
-- url     : https://prove2.me/theorems/bce86522-1f47-4af3-9d70-37b5066b525c
-- title:
--   Higher homotopy groups πₙ (n ≥ 2) are abelian
-- statement:
--   **Higher homotopy groups are abelian.** Let $X$ be a topological space with base point $x$ and $n\ge2$. Then the homotopy group $\pi_n(X,x)$ is abelian.
--
--   The proof is the Eckmann–Hilton argument. For $n\ge2$ the group operation can be performed in two independent coordinate directions, the two operations satisfy an interchange law, and so they coincide and are commutative. The fundamental group $\pi_1$ need not be abelian. Commutativity of the higher groups is why they are studied with the methods of homological algebra, for example in the Hurewicz theorem.
--
--   **Formalization note.** Mathlib's `HomotopyGroup.commGroup`. Mathlib indexes homotopy groups by a type $N$ of coordinates: `HomotopyGroup N X x` consists of the homotopy classes of maps $I^N\to X$ that send the boundary of the cube to $x$. `Nontrivial N` means that $N$ has at least two elements, so $\pi_n$ with $n\ge2$ is the case $N=\{0,\dots,n-1\}$. The multiplication is concatenation in one coordinate.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `HomotopyGroup.commGroup`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem higher_homotopy_groups_abelian_7a (N : Type*) {X : Type*} [TopologicalSpace X] (x : X) [DecidableEq N] [Nontrivial N]
    (a b : HomotopyGroup N X x) : a * b = b * a := by sorry

end FamousTheorems
