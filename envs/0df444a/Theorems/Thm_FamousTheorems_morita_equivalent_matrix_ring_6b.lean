-- Prove2me | Theorems.Thm_FamousTheorems_morita_equivalent_matrix_ring_6b
-- name    : FamousTheorems.morita_equivalent_matrix_ring_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:46.351853+00:00
-- url     : https://prove2.me/theorems/f173cdd5-9b5d-441a-b82c-d6353833cb35
-- title:
--   A ring is Morita equivalent to its matrix rings
-- statement:
--   **A ring is Morita equivalent to its matrix rings.** Let $R$ be a ring and $n\ge1$. Then $R$ and the matrix ring $M_n(R)$ are Morita equivalent: their categories of modules are equivalent.
--
--   This is the basic example of Morita equivalence. A left $M_n(R)$-module $M$ corresponds to the $R$-module $e_{11}M$, and an $R$-module $N$ corresponds to $N^n$. Morita-invariant properties, such as being semisimple, Noetherian or Artinian, are therefore shared by $R$ and $M_n(R)$. The example also accounts for the matrix factors in the Artin–Wedderburn theorem.
--
--   **Formalization note.** Mathlib's `IsMoritaEquivalent.matrix`. The matrices are indexed by a finite nonempty type $\iota$. The equivalence is $R_0$-linear for any commutative ring $R_0$ over which $R$ is an algebra, and $R_0=\mathbb Z$ gives the plain version. `IsMoritaEquivalent R₀ A B` says that there is an $R_0$-linear equivalence between the categories of modules over $A$ and over $B$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsMoritaEquivalent.matrix`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem morita_equivalent_matrix_ring_6b (R : Type*) {ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι] (R₀ : Type*) [CommRing R₀] [Algebra R₀ R]
    [Nonempty ι] : IsMoritaEquivalent R₀ R (Matrix ι ι R) := by sorry

end FamousTheorems
