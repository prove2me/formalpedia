-- Prove2me | Theorems.Thm_Deformation_exists_eq_smul_one_of_commute
-- name    : Deformation.exists_eq_smul_one_of_commute
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/d02951a5-4385-5726-873b-99e6f5726a79
-- title:
--   Schur's lemma for lifts of an absolutely irreducible representation
-- statement:
--   Let $n$ be a finite index type, $G$ a group and $k$ a field (with $G$ and $k$ in the same universe), let $A$ be a commutative local ring, and let $\pi \colon A \to k$ be a surjective ring homomorphism. Let $\rho' \colon G \to \mathrm{GL}_n(A)$ and $\rho_0 \colon G \to \mathrm{GL}_n(k)$ be group homomorphisms. Assume that the linear representation of $G$ on $k^n$ attached to $\rho_0$ — namely [`Deformation.matrixRepresentation`](def/Deformations_MatrixRepresentation.html#L15), the composite of $\rho_0$ with the passage from an invertible matrix to the corresponding linear automorphism of $n \to k$ and then to its underlying endomorphism — is absolutely irreducible in the sense of the class [`Representation.IsAbsolutelyIrreducible`](def/Representation_AbsolutelyIrreducible.html#L27): for every field $k'$ in the universe of $k$ equipped with a $k$-algebra structure, the base change of that representation to $k'$ is irreducible. Assume further that $\rho'$ lifts $\rho_0$ entrywise, i.e. applying $\pi$ to each entry of the matrix $\rho'(g)$ yields the matrix $\rho_0(g)$ for every $g \in G$. Then for every $M \in M_n(A)$ satisfying $\rho'(g) M = M \rho'(g)$ for all $g \in G$, there exists $a \in A$ with $M = a \cdot 1_n$. No completeness, Noetherian or topological hypothesis on $A$ is imposed.
--
--   This is the Schur-type lemma of deformation theory: the centraliser of a lift of an absolutely irreducible residual representation consists of scalars, which is what makes the conjugation action of the kernel of $\mathrm{GL}_n(A) \to \mathrm{GL}_n(k)$ on lifts free modulo the centre. It is used in the project via [`Deformation.exists_residuallyTrivial_conj_of_conj`](thm.html#Deformation.exists_residuallyTrivial_conj_of_conj) on the way to representability of the deformation functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_exists_eq_smul_one_of_commute.lean

import Mathlib
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_Representation_AbsolutelyIrreducible

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory IsLocalRing

universe u v

theorem Deformation.exists_eq_smul_one_of_commute {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G]
    {k : Type u} [Field k] {A : Type v} [CommRing A] [IsLocalRing A] (π : A →+* k) (hπ : Function.Surjective π)
    (ρ' : G →* GL n A) (ρ₀ : G →* GL n k)
    [Representation.IsAbsolutelyIrreducible.{u} (Deformation.matrixRepresentation ρ₀)]
    (hlift : ∀ g, ((ρ' g : GL n A) : Matrix n n A).map π = ((ρ₀ g : GL n k) : Matrix n n k))
    (M : Matrix n n A) (hM : ∀ g, ((ρ' g : GL n A) : Matrix n n A) * M = M * ((ρ' g : GL n A) : Matrix n n A)) :
    ∃ a : A, M = a • (1 : Matrix n n A) := by sorry
