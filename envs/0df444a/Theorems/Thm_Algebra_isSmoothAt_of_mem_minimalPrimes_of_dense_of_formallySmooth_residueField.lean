-- Prove2me | Theorems.Thm_Algebra_isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField
-- name    : Algebra.isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/47a97bbe-8c79-51fc-8345-b97b81530a50
-- title:
--   Generic smoothness from dense points with separable residue fields
-- statement:
--   Let $k$ be a field and let $B$ be a commutative $k$-algebra which is of finite type over $k$ and reduced (all in one universe $u$). Let $S$ be a set of points of $\operatorname{Spec} B$ subject to two hypotheses. First, a density hypothesis: every $g \in B$ which lies in the prime ideal $\mathfrak s$ of each point of $S$ is zero. Second, a separability hypothesis on residue fields: for every $\mathfrak s \in S$ there exist a field $K$ and a $k$-algebra structure on $K$ such that $K$ is formally smooth over $k$ and there is at least one $k$-algebra homomorphism from the residue field $\kappa(\mathfrak s) = B_{\mathfrak s}/\mathfrak s B_{\mathfrak s}$ of $\mathfrak s$ into $K$. Let finally $\mathfrak q$ be a prime ideal of $B$ belonging to $\operatorname{minimalPrimes} B$. The conclusion is `Algebra.IsSmoothAt k 𝔮`, i.e. the localisation $B_{\mathfrak q}$ is a formally smooth $k$-algebra; since $\mathfrak q$ is a minimal prime of a reduced ring, $B_{\mathfrak q}$ is the function field of the corresponding irreducible component of $\operatorname{Spec} B$.
--
--   This is the generic-smoothness criterion in the form used in Néron's smoothening process: a reduced finite-type $k$-scheme carrying a dense family of points whose residue fields embed into formally smooth (separable in the sense of Mac Lane) extensions of $k$ is smooth over $k$ at every generic point. It is cited by [`Algebra.isOpen_setOf_isSmoothAt_and_mem_freeLocus_and_minimalPrimes_subset`](thm.html#Algebra.isOpen_setOf_isSmoothAt_and_mem_freeLocus_and_minimalPrimes_subset), which turns this pointwise statement into an openness (hence density) statement about the smooth locus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Algebra.isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField
    {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsReduced B]
    (S : Set (PrimeSpectrum B))
    (hdense : ∀ g : B, (∀ 𝔰 ∈ S, g ∈ 𝔰.asIdeal) → g = 0)
    (hsep : ∀ 𝔰 ∈ S, ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      Algebra.FormallySmooth k K ∧ Nonempty (𝔰.asIdeal.ResidueField →ₐ[k] K))
    (𝔮 : Ideal B) [𝔮.IsPrime] (h𝔮 : 𝔮 ∈ minimalPrimes B) :
    Algebra.IsSmoothAt k 𝔮 := by sorry
