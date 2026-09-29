-- Prove2me | Theorems.Thm_Deformation_exists_residuallyTrivial_conj_of_conj
-- name    : Deformation.exists_residuallyTrivial_conj_of_conj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/76bad38b-207f-5c67-87a6-1222b76da16a
-- title:
--   Conjugate lifts are strictly equivalent, residually absolutely irreducible case
-- statement:
--   Let $n$ be a finite type with decidable equality, $G$ a group, $k$ a field (both in universe $u$), and $A$ a commutative local ring. Let $\pi : A \to k$ be a surjective ring homomorphism, and let $\rho_0 : G \to \mathrm{GL}_n(k)$ be a group homomorphism whose associated linear representation [`Deformation.matrixRepresentation`](def/Deformations_MatrixRepresentation.html#L15) $\rho_0$ of $G$ on $n \to k$ is absolutely irreducible in the sense of the project's class, namely that for every field $k'$ in universe $u$ equipped with a $k$-algebra structure the base change $k' \otimes \rho_0$ is irreducible. Let $\rho_1, \rho_2 : G \to \mathrm{GL}_n(A)$ be group homomorphisms, each lifting $\rho_0$ in the strict sense that for every $g \in G$ the entrywise image under $\pi$ of the matrix of $\rho_i(g)$ equals the matrix of $\rho_0(g)$. Suppose there is $g \in \mathrm{GL}_n(A)$ with $g\,\rho_1(x)\,g^{-1} = \rho_2(x)$ for all $x \in G$. Then there exists $\gamma \in \mathrm{GL}_n(A)$ whose matrix reduces entrywise under $\pi$ to the identity matrix and which satisfies $\gamma\,\rho_1(x)\,\gamma^{-1} = \rho_2(x)$ for all $x \in G$.
--
--   This is the standard comparison, going back to Mazur's foundational treatment of deformation rings, between isomorphism of lifts of a residually absolutely irreducible representation over $A$ and strict equivalence, i.e. conjugation by the kernel of $\mathrm{GL}_n(A) \to \mathrm{GL}_n(k)$. It is used in the universal deformation ring interface, where the deformation functor is defined by conjugation by residually trivial matrices while representability arguments produce only abstract isomorphisms; it is cited in the proof of [`GaloisRep.algHom_unique_of_baseChangeAlong_isEquiv_of_corepresentableBy`](thm.html#GaloisRep.algHom_unique_of_baseChangeAlong_isEquiv_of_corepresentableBy).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_exists_residuallyTrivial_conj_of_conj.lean

import Mathlib
import Definitions.Def_Representation_AbsolutelyIrreducible
import Definitions.Def_Deformations_MatrixRepresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem Deformation.exists_residuallyTrivial_conj_of_conj
    {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G]
    {k : Type u} [Field k] {A : Type v} [CommRing A] [IsLocalRing A]
    (π : A →+* k) (hπ : Function.Surjective π)
    (ρ₀ : G →* GL n k) [Representation.IsAbsolutelyIrreducible.{u} (Deformation.matrixRepresentation ρ₀)]
    (ρ₁ ρ₂ : G →* GL n A)
    (h₁ : ∀ g, ((ρ₁ g : GL n A) : Matrix n n A).map π = ((ρ₀ g : GL n k) : Matrix n n k))
    (h₂ : ∀ g, ((ρ₂ g : GL n A) : Matrix n n A).map π = ((ρ₀ g : GL n k) : Matrix n n k))
    (g : GL n A) (hg : ∀ x, g * ρ₁ x * g⁻¹ = ρ₂ x) :
    ∃ γ : GL n A, ((γ : GL n A) : Matrix n n A).map π = 1 ∧ ∀ x, γ * ρ₁ x * γ⁻¹ = ρ₂ x := by sorry
