-- Prove2me | Theorems.Thm_CvitanicKaratzas92_Optimality_theorem_9_1
-- name    : CvitanicKaratzas92.Optimality.theorem_9_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:14:46.057334+00:00
-- url     : https://prove2.me/theorems/53cf355b-e98f-405f-8e96-69b324b9cb52
-- title:
--   Theorem 9.1 — a claim whose $\mathcal M_\nu$-price is maximal at $\lambda\in\mathcal D$ is hedged by a $K$-valued portfolio
-- statement:
--   Under the standing assumptions, let $c$ be a consumption process, $B$ a positive $\mathcal F_T$-measurable random variable, and suppose there exists a process $\lambda\in\mathcal D$ such that
--   $$E\Big[H_\nu(T)B+\int_0^TH_\nu(s)c(s)\,ds\Big]\le E\Big[H_\lambda(T)B+\int_0^TH_\lambda(s)c(s)\,ds\Big]=:x<\infty\qquad\forall\,\nu\in\mathcal D. \tag{9.5}$$
--   Then there exists a portfolio process $\pi$ such that $(\pi,c)\in\mathcal A_0(x)$, $\pi(t,\omega)\in K$ for $\ell\otimes P$-a.e. $(t,\omega)$, and $X^{x,\pi,c}(T)=B$ a.s.
--
--   This extends Proposition 7.3 to the hedging of contingent claims by constrained portfolios, and gives the implication (E) $\Rightarrow$ (B) of Theorem 10.1.
--
--   **Formalization Note** The page concludes that "the pair $(\pi,c)$ belongs to the class $\mathcal A'(x)$ of (6.4)". The class $\mathcal A'(x)$ also carries the utility condition (6.2), which involves $U_1,U_2$; neither the hypotheses nor the proof of the theorem (pp. 781–785) involve utilities, and the proof establishes exactly admissibility, (9.1) and $X(T)=B$. The statement therefore concludes $(\pi,c)\in\mathcal A_0(x)$ together with (9.1). $x$ is a real number; positivity of $B$ is required almost surely.
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), pp. 780–781, Theorem 9.1

import Mathlib
import Definitions.Def_CvitanicKaratzas92_Optimality_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Optimality

/-- Cvitanić–Karatzas (1992), Theorem 9.1, pp. 780–781. Let `c` be a consumption process, `B` a
positive `𝓕_T`-measurable random variable, and suppose some `λ ∈ 𝒟` satisfies (9.5):
`E[H_ν(T)B + ∫₀ᵀ H_ν(s)c(s) ds] ≤ E[H_λ(T)B + ∫₀ᵀ H_λ(s)c(s) ds] =: x < ∞` for all `ν ∈ 𝒟`.
Then there is a portfolio `π` with `(π, c) ∈ 𝒜₀(x)`, `π ∈ K` `ℓ ⊗ P`-a.e., and
`X^{x,π,c}(T) = B` a.s. (The page writes "`𝒜'(x)` of (6.4)"; see the Formalization Note.) -/
theorem theorem_9_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) → ℝ≥0 → Ω → ℝ)
    (M : Market Ω d) (K : Set (EuclideanSpace ℝ (Fin d)))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (hS : Standing P 𝓕 T W I M K U1 U2)
    (c : ℝ≥0 → Ω → ℝ) (hc : IsConsumption 𝓕 P T c)
    (B : Ω → ℝ) (hBm : Measurable[𝓕 T] B) (hBpos : ∀ᵐ ω ∂P, 0 < B ω)
    (lam : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hlam : IsD P 𝓕 T K lam) (x : ℝ)
    (hx : ∫⁻ ω, (ENNReal.ofReal (HNu I M K lam T ω * B ω) +
      ∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (HNu I M K lam s.toNNReal ω * c s.toNNReal ω)) ∂P =
        ENNReal.ofReal x)
    (h95 : ∀ ν, IsD P 𝓕 T K ν →
      ∫⁻ ω, (ENNReal.ofReal (HNu I M K ν T ω * B ω) +
        ∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (HNu I M K ν s.toNNReal ω * c s.toNNReal ω)) ∂P ≤
      ENNReal.ofReal x) :
    ∃ (π : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (X : ℝ≥0 → Ω → ℝ),
      ⟨π, c, X⟩ ∈ A0 P 𝓕 T I M x ∧
      (∀ᵐ q ∂(lebP P T), π q.1.toNNReal q.2 ∈ K) ∧
      ∀ᵐ ω ∂P, X T ω = B ω := by sorry


end CvitanicKaratzas92.Optimality
