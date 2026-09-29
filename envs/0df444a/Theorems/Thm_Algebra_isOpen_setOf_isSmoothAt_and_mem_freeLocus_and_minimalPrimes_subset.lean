-- Prove2me | Theorems.Thm_Algebra_isOpen_setOf_isSmoothAt_and_mem_freeLocus_and_minimalPrimes_subset
-- name    : Algebra.isOpen_setOf_isSmoothAt_and_mem_freeLocus_and_minimalPrimes_subset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/435e551f-62c8-5fe8-9d3c-3552bc98ca7b
-- title:
--   Openness of the smooth-and-free locus; minimal primes lie in it
-- statement:
--   Let $k$ be a field, $A$ a commutative ring, $M$ a finitely presented $A$-module and $J$ an ideal of $A$ such that the quotient $B := A/J$ carries a $k$-algebra structure making it a finite-type, reduced $k$-algebra (all in one universe $u$). Let $S$ be a set of primes of $B$ subject to two hypotheses: a density condition, namely that any $g \in B$ belonging to $\mathfrak{s}$ for every $\mathfrak{s} \in S$ is zero; and a separability condition, namely that for each $\mathfrak{s} \in S$ there exist a field $K$ and a $k$-algebra structure on $K$ such that $K$ is formally smooth over $k$ and the residue field of $\mathfrak{s}$ admits a $k$-algebra homomorphism into $K$. The conclusion is the conjunction of two assertions about the set of those $\mathfrak{q} \in \operatorname{Spec} B$ at which $B$ is smooth over $k$ (in the sense `Algebra.IsSmoothAt`) and at which the base-changed module $B \otimes_A M$ lies in `Module.freeLocus`: first, this set is open in $\operatorname{Spec} B$; second, every $\mathfrak{q}$ whose underlying ideal is a minimal prime of $B$ belongs to it.
--
--   This is the openness and generic-point statement for the "good locus" of a reduced finite-type algebra equipped with a dense set of primes with separable residue fields, the locus where the algebra is smooth and a given finitely presented module becomes free after base change. It is used in the Néron model infrastructure, in [`NeronModelInfra.exists_opens_inter_closure_eq_setOf_isSmoothAt_and_mem_freeLocus`](thm.html#NeronModelInfra.exists_opens_inter_closure_eq_setOf_isSmoothAt_and_mem_freeLocus), where the algebra is a coordinate ring of a stratum and the module is a module of differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_isOpen_setOf_isSmoothAt_and_mem_freeLocus_and_minimalPrimes_subset.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct

universe u

theorem Algebra.isOpen_setOf_isSmoothAt_and_mem_freeLocus_and_minimalPrimes_subset
    {k : Type u} [Field k] {A : Type u} [CommRing A] (M : Type u) [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] (J : Ideal A)
    [Algebra k (A ⧸ J)] [Algebra.FiniteType k (A ⧸ J)] [IsReduced (A ⧸ J)]
    (S : Set (PrimeSpectrum (A ⧸ J)))
    (hdense : ∀ g : A ⧸ J, (∀ 𝔰 ∈ S, g ∈ 𝔰.asIdeal) → g = 0)
    (hsep : ∀ 𝔰 ∈ S, ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      Algebra.FormallySmooth k K ∧ Nonempty (𝔰.asIdeal.ResidueField →ₐ[k] K)) :
    IsOpen {𝔮 : PrimeSpectrum (A ⧸ J) | Algebra.IsSmoothAt k 𝔮.asIdeal ∧
      𝔮 ∈ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] M)} ∧
    ∀ 𝔮 : PrimeSpectrum (A ⧸ J), 𝔮.asIdeal ∈ minimalPrimes (A ⧸ J) →
      Algebra.IsSmoothAt k 𝔮.asIdeal ∧ 𝔮 ∈ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] M) := by sorry
