-- Prove2me | Theorems.Thm_FamousTheorems_character_orthonormality
-- name    : FamousTheorems.character_orthonormality
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:22:59.263986+00:00
-- url     : https://prove2.me/theorems/b5c62503-8920-4e1e-b642-08d07f7af3a6
-- title:
--   Orthonormality of irreducible characters
-- statement:
--   **Orthonormality of irreducible characters.** Let $G$ be a finite group and $k$ an algebraically closed field whose characteristic does not divide $|G|$. For irreducible finite-dimensional representations $V,W$ of $G$ over $k$,
--   $$\frac1{|G|}\sum_{g\in G}\chi_V(g)\,\chi_W(g^{-1})=\begin{cases}1&V\cong W,\\0&\text{otherwise.}\end{cases}$$
--
--   This is the first orthogonality relation of character theory. It shows that the irreducible characters are linearly independent, that a representation is determined by its character, and that the multiplicities of irreducible constituents can be read off from inner products.
--
--   **Formalization note.** Mathlib's `FDRep.char_orthonormal`. Irreducibility is `CategoryTheory.Simple`, `V.character` is the character, and invertibility of $|G|$ in $k$ is `Invertible (Nat.card G : k)`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `FDRep.char_orthonormal`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped Classical

theorem character_orthonormality {k G : Type*} [Field k] [IsAlgClosed k] [Group G] [Fintype G] [Invertible (Nat.card G : k)]
    (V W : FDRep k G) [CategoryTheory.Simple V] [CategoryTheory.Simple W] :
    (Nat.card G : k)⁻¹ * ∑ g : G, V.character g * W.character g⁻¹ =
      if Nonempty (CategoryTheory.Iso V W) then 1 else 0 := by sorry

end FamousTheorems
