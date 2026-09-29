-- Prove2me | Theorems.Thm_AlgebraicClosure_exists_uniform_level_of_characters_unramified_outside
-- name    : AlgebraicClosure.exists_uniform_level_of_characters_unramified_outside
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/9c3a7667-b5f7-53d7-ba7d-618934989d69
-- title:
--   Uniform finite level for characters unramified outside S
-- statement:
--   Fix the algebraic closure $\bar{\mathbb{Q}}$ of $\mathbb{Q}$ and write $G = \mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$ for its group of $\mathbb{Q}$-algebra automorphisms; for an intermediate field $F$ of $\bar{\mathbb{Q}}/\mathbb{Q}$, membership of $\sigma$ in `F.fixingSubgroup` means that $\sigma$ fixes every element of $F$. Let $L'$ be an intermediate field of $\bar{\mathbb{Q}}/\mathbb{Q}$ which is a number field, let $p_0$ be a prime natural number, and let $S$ be a finite set of natural numbers. The assertion is that there exists an intermediate field $M$ of $\bar{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$ and containing $L'$, with the following property: every function $\chi \colon G \to \mathbb{Z}/p_0$ such that (i) $\chi(\sigma\tau) = \chi(\sigma) + \chi(\tau)$ whenever $\sigma$ and $\tau$ both fix $L'$ pointwise, (ii) there is an intermediate field $L_0$, finite-dimensional over $\mathbb{Q}$, with $\chi(\sigma) = 0$ for every $\sigma$ fixing $L_0$ pointwise, and (iii) for every prime $q \notin S$, every valuation subring $P$ of $\bar{\mathbb{Q}}$ with $q$ a nonunit of $P$, and every $\sigma$ lying in the image in $G$ of the inertia subgroup of $P$ inside its decomposition subgroup, one has $\chi(\sigma) = 0$ provided $\sigma$ fixes $L'$ pointwise, satisfies $\chi(\sigma) = 0$ for all $\sigma$ fixing $M$ pointwise. Thus the level $M$ is uniform in $\chi$.
--
--   This is the Hermite–Minkowski finiteness in its Kummer-theoretic form: the compositum of the $\mathbb{Z}/p_0$-extensions of a number field $L'$ unramified outside a finite set of rational primes is of finite degree, here packaged as a single finite level $M$ annihilating all such characters at once. It feeds the finiteness of tangent spaces of ramification-bounded deformation conditions and of continuous first cohomology, being cited by [`GaloisRep.tangentFinite_unramifiedOutside`](thm.html#GaloisRep.tangentFinite_unramifiedOutside), [`groupCohomology.finiteDimensional_continuousH1S`](thm.html#groupCohomology.finiteDimensional_continuousH1S) and [`ModularCurve.JZero.finiteIndex_range_nsmul_two_invariants`](thm.html#ModularCurve.JZero.finiteIndex_range_nsmul_two_invariants).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicClosure_exists_uniform_level_of_characters_unramified_outside.lean

import Definitions.Def_FLTPrelim_Ramification
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField IsDedekindDomain

theorem AlgebraicClosure.exists_uniform_level_of_characters_unramified_outside
    (L' : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L'] (p₀ : ℕ) (hp₀ : p₀.Prime)
    (S : Finset ℕ) :
    ∃ M : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ M ∧ L' ≤ M ∧
      ∀ χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ZMod p₀,
        (∀ σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          σ ∈ L'.fixingSubgroup → τ ∈ L'.fixingSubgroup → χ (σ * τ) = χ σ + χ τ) →
        (∃ L₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L₀ ∧
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ L₀.fixingSubgroup → χ σ = 0) →
        (∀ q : ℕ, q.Prime → q ∉ S → ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
          ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ ∈ L'.fixingSubgroup → χ σ = 0) →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ M.fixingSubgroup → χ σ = 0 := by sorry
