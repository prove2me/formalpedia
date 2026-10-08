-- Prove2me | Theorems.Thm_CvitanicKaratzas92_Optimality_proposition_8_3
-- name    : CvitanicKaratzas92.Optimality.proposition_8_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:13:38.135006+00:00
-- url     : https://prove2.me/theorems/4ee74372-e977-4dca-b4e3-7dd262e0bab2
-- title:
--   Proposition 8.3 — if $\pi_\lambda\in K$ and $\delta(\lambda)+\pi_\lambda^*\lambda=0$, then $(\pi_\lambda,c_\lambda)$ is optimal for the constrained problem
-- statement:
--   Under the standing assumptions, let $x>0$, $\lambda\in\mathcal D'$ and $y=\mathcal Y_\lambda(x)$. Let $\pi_\lambda$ be the portfolio of (8.20): together with $c_\lambda$ it finances the process $X_\lambda$ of (8.19) in $\mathcal M_\lambda$, i.e. $X_\lambda$ solves (8.10) with $\nu=\lambda$, $\pi=\pi_\lambda$, $c=c_\lambda$. Suppose that for $\ell\otimes P$-a.e. $(t,\omega)$
--   $$\pi_\lambda(t,\omega)\in K, \tag{8.21}$$
--   $$\delta(\lambda(t,\omega))+\pi_\lambda^*(t,\omega)\lambda(t,\omega)=0. \tag{8.22}$$
--   Then the pair $(\pi_\lambda,c_\lambda)$ belongs to $\mathcal A'(x)$, is optimal for the constrained optimization problem (6.5) in the original market $\mathcal M$, and satisfies
--   $$E\Big[\int_0^TU_1(t,c_\lambda(t))\,dt+U_2(\xi_\lambda)\Big]\le V_\nu(x)\qquad\forall\,\nu\in\mathcal D. \tag{8.23}$$
--
--   This embeds the constrained problem in the family of auxiliary problems and is the implication (B) $\Rightarrow$ (A), (C) of Theorem 10.1.
--
--   **Formalization Note** "$\pi_\lambda$ is the portfolio of (8.20)" becomes: $\pi_\lambda$ is a portfolio process and a continuous process $X$ with $X(t)=X_\lambda(t)$ a.s. for every $t\le T$ solves the $\mathcal M_\lambda$ wealth equation with $(\pi_\lambda,c_\lambda)$. The conclusion is stated for the triple $(\pi_\lambda,c_\lambda,X)$, $X$ being its wealth in $\mathcal M$. (8.22) is an extended-real equation; $y$ is a binder with $\mathcal X_\lambda(y)=x$.
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), p. 779, Proposition 8.3 (with (8.17)–(8.20), p. 778)

import Mathlib
import Definitions.Def_CvitanicKaratzas92_Optimality_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Optimality

/-- Cvitanić–Karatzas (1992), Proposition 8.3, p. 779. Let `λ ∈ 𝒟'`, `y = 𝒴_λ(x)`, and let
`π_λ` be the portfolio of (8.20): with `c_λ` it finances (a continuous version `X` of) `X_λ`
in `𝓜_λ`. If (8.21) `π_λ ∈ K` and (8.22) `δ(λ) + π_λ*λ = 0` hold `ℓ ⊗ P`-a.e., then
`(π_λ, c_λ)` (with wealth `X`) belongs to `𝒜'(x)`, is optimal for (6.5), and satisfies
(8.23) `E[∫₀ᵀ U₁(t, c_λ(t)) dt + U₂(ξ_λ)] ≤ V_ν(x)` for every `ν ∈ 𝒟`. -/
theorem proposition_8_3 {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) → ℝ≥0 → Ω → ℝ)
    (M : Market Ω d) (K : Set (EuclideanSpace ℝ (Fin d)))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (hS : Standing P 𝓕 T W I M K U1 U2)
    (x : ℝ) (hx : 0 < x) (lam : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hlam : IsD' P 𝓕 T I M K U1 U2 lam) (y : ℝ) (hy : 0 < y)
    (hxy : calX P T I M K U1 U2 lam y = ENNReal.ofReal x)
    (πlam : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (X : ℝ≥0 → Ω → ℝ)
    (hπ : IsPortfolio 𝓕 P T πlam)
    (hX : IsWealthNu P 𝓕 T I M K lam x πlam (cNu I M K U1 lam y) X)
    (hXver : ∀ t ≤ T, ∀ᵐ ω ∂P, X t ω = XNu P 𝓕 T I M K U1 U2 lam y t ω)
    (h821 : ∀ᵐ q ∂(lebP P T), πlam q.1.toNNReal q.2 ∈ K)
    (h822 : ∀ᵐ q ∂(lebP P T), delta K (lam q.1.toNNReal q.2) +
      ((inner ℝ (πlam q.1.toNNReal q.2) (lam q.1.toNNReal q.2) : ℝ) : EReal) = 0) :
    (⟨πlam, cNu I M K U1 lam y, X⟩ : Triple Ω d) ∈ A' P 𝓕 T I M K U1 U2 x ∧
    (∀ τ ∈ A' P 𝓕 T I M K U1 U2 x,
      J P T U1 U2 τ ≤ J P T U1 U2 ⟨πlam, cNu I M K U1 lam y, X⟩) ∧
    ∀ ν, IsD P 𝓕 T K ν →
      expUtil P T U1 U2 (cNu I M K U1 lam y) (xiNu T I M K U2 lam y) ≤
        Vnu P 𝓕 T I M K U1 U2 ν x := by sorry


end CvitanicKaratzas92.Optimality
