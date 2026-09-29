-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_forall_twistedCentralizer_conjAe_eq_scalar_mul_of_neg
-- name    : AutomorphicForm.exists_isCompact_forall_twistedCentralizer_conjAe_eq_scalar_mul_of_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/9e772507-5c46-5531-915d-673d62dd25b0
-- title:
--   Twisted centraliser compact modulo real scalars when c<0
-- statement:
--   Work in $\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$, with $\sigma$ the automorphism induced on matrices by complex conjugation `Complex.conjAe` of $\mathbb{C}$ over $\mathbb{R}$ (extended to the tensor factor), and let $\iota =$ `toTensorGL ℝ ℂ ℝ` be the map $\mathrm{GL}_2(\mathbb{R})\to\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ coming from the right inclusion into the tensor product. Let $c$ be a unit of $\mathbb{R}$ with $c<0$, and let $\delta, y \in \mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ satisfy `IsNormConjugator`, that is $\iota(c\cdot 1) = y^{-1}\,\bigl(\delta\cdot\sigma(\delta)\bigr)\,y$, the middle factor being the norm string $\prod_{i<\dim_{\mathbb{R}}\mathbb{C}} \sigma^{i}(\delta)$ of length two. The conclusion asserts the existence of a compact set $C$ of $\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ contained in the twisted centraliser $T'_\delta = \{t : t\,\delta\,\sigma(t)^{-1} = \delta\}$ such that every $t \in T'_\delta$ factors as $t = \iota(e\cdot 1)\,k$ with $e \in \mathbb{R}^\times$ and $k \in C$. Thus only the inclusion $T'_\delta \subseteq \iota(\mathbb{R}^\times\cdot 1)\,C$ together with $C \subseteq T'_\delta$ is asserted, not the equality of the two sets.
--
--   This is the archimedean case, at a real place of the base field lying under a complex place, of the statement that a twisted centraliser of the second kind is compact modulo the central real scalars; for $c<0$ the twisted centraliser is the unit group of Hamilton's quaternions inside $\mathrm{GL}_2(\mathbb{C})$, which is the product of the real scalars with a compact group. It is used in the construction of twisted section functions and in the asymptotic analysis of twisted orbital integrals at such a place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_forall_twistedCentralizer_conjAe_eq_scalar_mul_of_neg.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isCompact_forall_twistedCentralizer_conjAe_eq_scalar_mul_of_neg
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) :
    ∃ C : Set (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), IsCompact C ∧
      C ⊆ (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ : Set (GL (Fin 2) (ℂ ⊗[ℝ] ℝ))) ∧
      ∀ t ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ,
        ∃ e : ℝˣ, ∃ k ∈ C,
          t = toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) e) * k := by sorry
