-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgFin_localization_iff_of_forall_mem_iff
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_bijective_primes_chartAlgFin_localization_iff_of_forall_mem_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/535df8dd-c178-5c55-97bf-005111413e2a
-- title:
--   Transport of primes of the finite chart ring along an automorphism
-- statement:
--   Let $A$ be a commutative ring, $T$ a field which is an $A$-algebra, and $j \in T$; write $B =$ `chartAlgFin A T j` for the subalgebra of $T$ consisting of the elements integral over $A[j] =$ `Algebra.adjoin A {j}`, i.e. the integral closure of $A[j]$ in $T$. Let $\sigma$ be an $A$-algebra automorphism of $T$ such that for every $b \in T$ one has $b \in B$ if and only if $\sigma b \in B$. Then there exists a map $\Phi$ from the set of prime ideals of $B$ to itself with the following four properties: $\Phi$ is bijective; for all primes $y_1, y_2$ one has $y_1 \subseteq y_2$ if and only if $\Phi y_1 \subseteq \Phi y_2$; for every prime $y$ and every $b \in B$, $b \in \Phi y$ if and only if $\sigma^{-1} b \in y$ (the hypothesis on $\sigma$ providing the membership $\sigma^{-1}b \in B$); and, for every prime $y$ and every $f \in T$, first, $f$ can be written as $g/h$ with $g, h \in B$ and $h \notin \Phi y$ if and only if $\sigma^{-1} f$ can be so written with $h \notin y$, and second, the same equivalence holds with the additional requirement $g \in \Phi y$, respectively $g \in y$.
--
--   This is the elementary transport of the spectrum and of the local rings of a ring along an automorphism, stated for the finite chart ring of the two-chart integral model and phrased directly in the membership predicates describing the local ring $B_y \subseteq T$ and its maximal ideal, so that it applies to the stalks of that model. It is used in the analysis of how level automorphisms of a modular curve move points of the finite chart, the relevant automorphisms stabilising $B$ because they fix an element mutually integral with $j$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgFin_localization_iff_of_forall_mem_iff.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.TwoChartIntegralModel.exists_bijective_primes_chartAlgFin_localization_iff_of_forall_mem_iff
    {A : Type} [CommRing A] {T : Type} [Field T] [Algebra A T] (j : T)
    (σ : T ≃ₐ[A] T)
    (hσ : ∀ b : T, b ∈ TwoChartIntegralModel.chartAlgFin A T j ↔ σ b ∈ TwoChartIntegralModel.chartAlgFin A T j) :
    ∃ Φ : {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime} →
            {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime},
      Function.Bijective Φ ∧
      (∀ y₁ y₂ : {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime},
        y₁.1 ≤ y₂.1 ↔ (Φ y₁).1 ≤ (Φ y₂).1) ∧
      (∀ (y : {y : Ideal ↥(TwoChartIntegralModel.chartAlgFin A T j) // y.IsPrime})
        (b : ↥(TwoChartIntegralModel.chartAlgFin A T j)),
        b ∈ (Φ y).1 ↔ (⟨σ.symm b, (hσ (σ.symm b)).2 (by rw [AlgEquiv.apply_symm_apply]; exact b.2)⟩ :
          ↥(TwoChartIntegralModel.chartAlgFin A T j)) ∈ y.1) ∧
      (∀ y (f : T),
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgFin A T j), h ∉ (Φ y).1 ∧ f * (h : T) = (g : T)) ↔
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgFin A T j), h ∉ y.1 ∧ σ.symm f * (h : T) = (g : T))) ∧
      (∀ y (f : T),
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgFin A T j), h ∉ (Φ y).1 ∧ g ∈ (Φ y).1 ∧ f * (h : T) = (g : T)) ↔
        (∃ g h : ↥(TwoChartIntegralModel.chartAlgFin A T j), h ∉ y.1 ∧ g ∈ y.1 ∧ σ.symm f * (h : T) = (g : T))) := by sorry
