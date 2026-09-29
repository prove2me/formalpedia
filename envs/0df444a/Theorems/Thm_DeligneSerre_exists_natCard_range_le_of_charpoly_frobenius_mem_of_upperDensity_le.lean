-- Prove2me | Theorems.Thm_DeligneSerre_exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le
-- name    : DeligneSerre.exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/dc9a06cb-43e3-590d-89e8-1dec16f86c51
-- title:
--   Deligne–Serre: uniform bound on mod-ℓ Galois images
-- statement:
--   Let $\eta$ be a real number with $\eta < 1/2$, let $M$ be a natural number and let $X$ be a set of natural numbers whose primes are sparse in the following explicit sense: for every $\delta > 0$ there is $s_0 > 1$ such that for all real $s$ with $1 < s < s_0$ one has $\sum_{p} p^{-s} \le (\eta + \delta)\log\bigl(1/(s-1)\bigr)$, the sum being over the primes belonging to $X$. Then there exists a natural number $A$ with the following property. Let $\ell$ be a prime and let $\rho \colon \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(\mathbb{Z}/\ell)$ be a group homomorphism, where $\overline{\mathbb{Q}}$ is the algebraic closure of $\mathbb{Q}$ and the Galois group is realised as the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$. Assume that $\rho$ factors through a finite level, i.e. there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that $\rho\sigma = 1$ for every $\sigma$ fixing $L$ pointwise; and assume the associated linear representation of the Galois group on $(\mathbb{Z}/\ell)^2$, obtained by composing $\rho$ with the map from $\mathrm{GL}_2$ to linear endomorphisms, is semisimple. Let $S$ be a finite set of naturals and $P$ a finite set of polynomials over $\mathbb{Z}/\ell$ with at most $M$ elements, and suppose that for every prime $p \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $p$ (meaning $p$ is a nonunit of $A$): firstly $\rho$ is trivial on the image in the Galois group of the inertia subgroup of $A$ over $\mathbb{Q}$, and secondly, provided $p \notin X$, for every $\sigma$ in the decomposition subgroup of $A$ acting on the residue field of $A$ by $x \mapsto x^p$, the characteristic polynomial of the matrix $\rho\sigma$ lies in $P$. Then the cardinality of the image of $\rho$ is at most $A$.
--
--   This is the group-theoretic and Chebotarev input of Lemmes 8.3–8.4 of Deligne–Serre, isolated as a uniform bound, independent of the residue characteristic $\ell$, on the order of the image of a semisimple mod-$\ell$ representation of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ whose Frobenius characteristic polynomials take at most $M$ values outside a sparse set of primes. It feeds the construction of the $\ell$-adic, and then complex, Galois representation attached to a weight one Hecke eigenform, namely [`DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen`](thm.html#DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DeligneSerre_exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_Deformations_MatrixRepresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial
open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem DeligneSerre.exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le
    (η : ℝ) (hη : η < 1 / 2) (M : ℕ) (X : Set ℕ)
    (hX : ∀ δ : ℝ, 0 < δ → ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
      ∑' p : {p : ℕ // p.Prime ∧ p ∈ X}, ((p : ℕ) : ℝ) ^ (-s) ≤
        (η + δ) * Real.log (1 / (s - 1))) :
    ∃ A : ℕ, ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ρ : Γℚ →* GL (Fin 2) (ZMod ℓ)),
      GaloisFactorsThroughFiniteLevel ρ →
      (Deformation.matrixRepresentation ρ).IsSemisimpleRepresentation →
      ∀ (S : Finset ℕ) (P : Finset (ZMod ℓ)[X]), P.card ≤ M →
        (∀ p : ℕ, p.Prime → p ∉ S →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
            (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
            ∀ σ : Γℚ, A.IsFrobeniusAt σ p → p ∉ X →
              ((ρ σ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).charpoly ∈ P) →
        Nat.card (MonoidHom.range ρ) ≤ A := by sorry
