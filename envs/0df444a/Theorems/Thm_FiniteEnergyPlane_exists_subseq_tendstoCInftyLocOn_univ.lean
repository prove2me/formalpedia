-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoCInftyLocOn_univ
-- name    : FiniteEnergyPlane.exists_subseq_tendstoCInftyLocOn_univ
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-25T18:16:51.635983+00:00
-- url     : https://prove2.me/theorems/4c27d83a-935d-4515-a10a-0e27857a6454
-- title:
--   $C^\infty_{\mathrm{loc}}$ compactness on the plane for pseudoholomorphic maps on growing discs
-- statement:
--   Let $E$ be a finite-dimensional real normed space and $J$ a smooth almost complex structure on an open set $O\subseteq E$. Let $\rho_k\to\infty$ and let $v_k:\mathbb C\to E$ be of class $C^1$ and $J$-holomorphic on the disc $B(0,\rho_k)$. Assume that for every $R$ there are a compact set $K\subseteq O$ and a constant $M$ such that, whenever $\rho_k>R$,
--   $$v_k\big(B(0,R)\big)\subseteq K\qquad\text{and}\qquad \|Dv_k(z)\|\le M\ \text{ for } z\in B(0,R).$$
--   Then there are a subsequence $(v_{k_j})$ and a smooth $J$-holomorphic map $w:\mathbb C\to O$ such that $v_{k_j}\to w$ in $C^\infty_{\mathrm{loc}}(\mathbb C)$: on every compact subset of $\mathbb C$ all derivatives converge uniformly.
--
--   It provides limit planes for sequences of pseudoholomorphic maps defined on discs of growing radius.
--
--   **Formalization Note** $C^\infty_{\mathrm{loc}}$ convergence is `JHolomorphic.TendstoCInftyLocOn` on `Set.univ` (uniform convergence of every `iteratedFDeriv ℝ m` on every compact set). Smoothness of $w$ is `ContDiff ℝ ∞ w`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Prop. 9.1 and Lecture 9; H. Hofer, Invent. Math. 114 (1993), Section 3

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- `C^∞_loc` compactness on the whole plane for pseudoholomorphic maps on growing discs. Let `J`
be a smooth almost complex structure on an open set `O` of a finite-dimensional real normed space
`E`, let `ρ_k → ∞`, and let `v_k` be `C¹` and `J`-holomorphic on `B(0, ρ_k)`. Assume that for every
`R` there are a compact `K ⊆ O` and a constant `M` such that `v_k(B(0, R)) ⊆ K` and
`‖Dv_k‖ ≤ M` on `B(0, R)` whenever `ρ_k > R`. Then a subsequence converges in `C^∞_loc(ℂ)` to a
smooth `J`-holomorphic map `w : ℂ → O`. -/
theorem exists_subseq_tendstoCInftyLocOn_univ {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (v : ℕ → ℂ → E) (ρ : ℕ → ℝ)
    (hρ : Tendsto ρ atTop atTop) (hv : ∀ k, ContDiffOn ℝ 1 (v k) (ball 0 (ρ k)))
    (hhol : ∀ k, JHolomorphic.IsJHolomorphicOn J (ball 0 (ρ k)) (v k))
    (hbd : ∀ R : ℝ, ∃ K : Set E, IsCompact K ∧ K ⊆ O ∧ ∃ M : ℝ, ∀ k, R < ρ k →
      ∀ z ∈ ball (0 : ℂ) R, v k z ∈ K ∧ ‖fderiv ℝ (v k) z‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → E, ContDiff ℝ ∞ w ∧
      JHolomorphic.IsJHolomorphicOn J Set.univ w ∧ (∀ z, w z ∈ O) ∧
      JHolomorphic.TendstoCInftyLocOn (fun j => v (φ j)) w Set.univ := by
  sorry

end FiniteEnergyPlane
