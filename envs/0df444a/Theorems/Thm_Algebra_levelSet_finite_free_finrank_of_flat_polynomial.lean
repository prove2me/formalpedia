-- Prove2me | Theorems.Thm_Algebra_levelSet_finite_free_finrank_of_flat_polynomial
-- name    : Algebra.levelSet_finite_free_finrank_of_flat_polynomial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/8d1e8536-51c7-5486-9702-393d0e1c6f91
-- title:
--   Level sets of a finite flat coordinate are free of rank d
-- statement:
--   Let $R$ be a commutative ring, $A$ a commutative $R$-algebra, $f$ an element of $A$ and $d$ a natural number (all types in a single universe). Regard $A$ as an $R[X]$-algebra via the evaluation map $\mathrm{aeval}\,f : R[X] \to A$, $X \mapsto f$, and assume: (i) the underlying ring homomorphism of $\mathrm{aeval}\,f$ is finite, i.e. $A$ is a finite $R[X]$-module; (ii) it is flat, i.e. $A$ is a flat $R[X]$-module; and (iii) for every field $L$ that is an $R$-algebra and every $x \in L$, the $L$-vector space $\bigl(L \otimes_R A\bigr)/\bigl(1 \otimes f - x \otimes 1\bigr)$ has finite rank exactly $d$. The conclusion is that for every commutative ring $S$ which is an $R$-algebra and is local, and every $s \in S$, the quotient ring $\bigl(S \otimes_R A\bigr)/\bigl(1 \otimes f - s \otimes 1\bigr)$, viewed as an $S$-module, is finite, free, and of rank $d$ (these three assertions being the three components of the conclusion).
--
--   This is the commutative-algebra form of the statement that the level sets of a finite flat coordinate $f \colon \operatorname{Spec} A \to \mathbb{A}^1_R$ of constant fibre degree $d$ are finite free of rank $d$ after base change to a local ring: the level-set ring is the base change of the finite flat $R[X]$-module $A$ along $R[X] \to S$, $X \mapsto s$. It supplies the "level sets free of rank $d$" clause used by [`AlgebraicGeometry.SmoothProperCurve.levelSet_free_of_twoChartPoleDatum`](thm.html#AlgebraicGeometry.SmoothProperCurve.levelSet_free_of_twoChartPoleDatum) and [`AlgebraicGeometry.SmoothProperCurve.levelSet_free_of_twoChartPoleDatum_of_forall_finrank`](thm.html#AlgebraicGeometry.SmoothProperCurve.levelSet_free_of_twoChartPoleDatum_of_forall_finrank), where a finite map from a curve to $\mathbb{P}^1$ is recorded chart by chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_levelSet_finite_free_finrank_of_flat_polynomial.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open Polynomial
open scoped TensorProduct

theorem Algebra.levelSet_finite_free_finrank_of_flat_polynomial
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] (f : A) (d : ℕ)
    (hfin : (Polynomial.aeval f : R[X] →ₐ[R] A).toRingHom.Finite)
    (hflat : (Polynomial.aeval f : R[X] →ₐ[R] A).toRingHom.Flat)
    (hrank : ∀ (L : Type u) [Field L] [Algebra R L] (x : L),
      Module.finrank L (L ⊗[R] A ⧸ Ideal.span {(1 : L) ⊗ₜ[R] f - x ⊗ₜ[R] (1 : A)}) = d) :
    ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
      Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ∧
        Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ∧
        Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) = d := by sorry
