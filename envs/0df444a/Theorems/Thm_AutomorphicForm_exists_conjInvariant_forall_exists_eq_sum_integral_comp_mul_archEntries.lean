-- Prove2me | Theorems.Thm_AutomorphicForm_exists_conjInvariant_forall_exists_eq_sum_integral_comp_mul_archEntries
-- name    : AutomorphicForm.exists_conjInvariant_forall_exists_eq_sum_integral_comp_mul_archEntries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/92b36fb5-d35f-5220-8bec-bae798f833c2
-- title:
--   Conjugation-invariant parametrix kernels on the archimedean matrix algebra
-- statement:
--   Let $K$ be a number field, write $A$ for the space $\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to$ `mixedEmbedding.mixedSpace K` of $2\times 2$ matrices with entries in the mixed space of $K$, a finite-dimensional real vector space carrying its default measure, and let $U \subseteq A$ be a neighbourhood of `archEntries K 1`, the entry matrix of the identity of $\mathrm{GL}_2$ of the infinite adele ring transported to the mixed space. The assertion is that there are a natural number $n$ and functions $\Psi_k : A \to \mathbb{C}$, $k \in \mathrm{Fin}\,n$, such that each $\Psi_k$ is continuous, has compact support with $\operatorname{tsupport} \Psi_k \subseteq U$, and is conjugation invariant in the following sense: for every infinite place $w$ of $K$, every $\kappa$ in the group `rowIsometrySubgroup₀ w.Completion` (a subgroup of $\mathrm{GL}_2$ of the completion $K_w$ defined by a row-isometry condition; the project's `IsRowIsometry` asks that the determinant have norm one and that $(x,y) \mapsto (x k_{00} + y k_{10},\, x k_{01} + y k_{11})$ preserve $\lVert x\rVert^2 + \lVert y\rVert^2$) and every $E \in A$, one has $\Psi_k(\mathrm{A}(\kappa)\, E\, \mathrm{A}(\kappa^{-1})) = \Psi_k(E)$, where $\mathrm{A}(\kappa) =$ `archEntries K (archRowIsometryInclAt₀ K w κ)` is the matrix over the mixed space obtained from the image of $\kappa$ in $\mathrm{GL}_2$ of the infinite adele ring at the place $w$; and moreover, for every $\Phi : A \to \mathbb{C}$ that is $C^\infty$ over $\mathbb{R}$, compactly supported, and whose support consists of matrices with invertible determinant, there exist $C^\infty$ functions $\Phi'_k : A \to \mathbb{C}$ with $\operatorname{tsupport} \Phi'_k \subseteq \operatorname{tsupport} \Phi$ and $\Phi(X) = \sum_{k} \int_A \Phi'_k(XE)\,\Psi_k(E)\,dE$ for all $X \in A$. The kernels $\Psi_k$, their number $n$, and their supports depend only on $U$, not on $\Phi$, and are required to be continuous only.
--
--   This is the archimedean parametrix input of Arthur's factorisation argument, in the form of a Dixmier–Malliavin-type decomposition of a smooth compactly supported function on the matrix algebra as a finite sum of right convolutions against fixed conjugation-invariant continuous kernels concentrated near the identity. It is used by [`AutomorphicForm.exists_eq_sum_rightConv_conjInvariant_principalLevel_of_isFactorizableTestFn`](thm.html#AutomorphicForm.exists_eq_sum_rightConv_conjInvariant_principalLevel_of_isFactorizableTestFn) to rewrite a factorizable test function of given principal level on $\mathrm{GL}_2$ of the adeles as such a sum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_conjInvariant_forall_exists_eq_sum_integral_comp_mul_archEntries.lean

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm MeasureTheory
open scoped Classical in

theorem AutomorphicForm.exists_conjInvariant_forall_exists_eq_sum_integral_comp_mul_archEntries
    (K : Type) [Field K] [NumberField K]
    (U : Set (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K)) (hU : U ∈ nhds (archEntries K 1)) :
    ∃ (n : ℕ) (Ψ : Fin n → (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ),
      (∀ k, Continuous (Ψ k) ∧ HasCompactSupport (Ψ k) ∧ tsupport (Ψ k) ⊆ U ∧
        ∀ (w : InfinitePlace K) (κ : rowIsometrySubgroup₀ w.Completion)
            (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K),
          Ψ k (Matrix.of.symm
              (Matrix.of (archEntries K (archRowIsometryInclAt₀ K w κ)) * Matrix.of E *
                Matrix.of (archEntries K (archRowIsometryInclAt₀ K w κ⁻¹)))) = Ψ k E) ∧
      ∀ Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
          tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} →
        ∃ Φ' : Fin n → (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ,
          (∀ k, ContDiff ℝ (⊤ : ℕ∞) (Φ' k) ∧ tsupport (Φ' k) ⊆ tsupport Φ) ∧
          ∀ X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K,
            Φ X = ∑ k, ∫ E, Φ' k (Matrix.of.symm (Matrix.of X * Matrix.of E)) * Ψ k E := by sorry
