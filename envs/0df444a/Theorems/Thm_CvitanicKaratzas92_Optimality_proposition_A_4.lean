-- Prove2me | Theorems.Thm_CvitanicKaratzas92_Optimality_proposition_A_4
-- name    : CvitanicKaratzas92.Optimality.proposition_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:23:46.484067+00:00
-- url     : https://prove2.me/theorems/59501a68-e60b-4980-bedf-6f1273c45c19
-- title:
--   Proposition A.4 — $\lambda=-\sigma[\mu+\psi/(M-A)]$ satisfies (8.22), $\int_0^T\|\lambda\|^2<\infty$, $\int_0^T\delta(\lambda)<\infty$
-- statement:
--   In the setting of Lemma A.2 (standing assumptions, (5.8), (8.25), (12.2), and $(\hat\pi,\hat c)$ with wealth $\hat X$ satisfying (A) for $x>0$; $A$ and $M$ as in (A.9)–(A.10)), let $\psi$ be the progressively measurable $\mathbb R^d$-valued process and $y_0$ the constant of the martingale representation
--   $$M(t)=y_0+\int_0^t\psi^*(s)\,dW(s),\qquad 0\le t\le T, \tag{A.10}$$
--   and let $\mu=\theta-\sigma^*\hat\pi$ (A.2). Then the process
--   $$\lambda(t)=-\sigma(t)\Big[\mu(t)+\frac{\psi(t)}{M(t)-A(t)}\Big],\qquad 0\le t\le T, \tag{A.20}$$
--   satisfies (8.22), $\delta(\lambda(t))+\lambda^*(t)\hat\pi(t)=0$ for $\ell\otimes P$-a.e. $(t,\omega)$, and
--   $$\int_0^T\|\lambda(t)\|^2dt<\infty,\qquad\int_0^T\delta(\lambda(t))\,dt<\infty\qquad\text{a.s.}$$
--
--   This produces the candidate dual process $\lambda$ in the proof of (A) $\Rightarrow$ (B).
--
--   **Formalization Note** $M$ is a progressively measurable version of the conditional expectation, and $\psi$ is locally square integrable with $M(t)=y_0+\int_0^t\psi^*dW$ a.s. for every $t\le T$, the stochastic integral given by the Itô-integral operator. The integral of $\delta(\lambda)$ is that of its positive part ($\delta$ is bounded below by (4.4)); (8.22) is an extended-real equation.
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), pp. 805–808, (A.2), (A.9)–(A.10), Proposition A.4

import Mathlib
import Definitions.Def_CvitanicKaratzas92_Optimality_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Optimality

/-- Cvitanić–Karatzas (1992), Proposition A.4, p. 808. In the setting of Lemma A.2, let
`ψ` and `y₀` give the martingale representation (A.10) `M(t) = y₀ + ∫₀ᵗ ψ*(s) dW(s)`, and let
(A.2) `μ = θ − σ*π̂`. Then the process (A.20) `λ(t) = −σ(t)[μ(t) + ψ(t)/(M(t) − A(t))]`
satisfies (8.22) `δ(λ(t)) + λ*(t)π̂(t) = 0` `ℓ ⊗ P`-a.e., and `∫₀ᵀ ‖λ(t)‖² dt < ∞`,
`∫₀ᵀ δ(λ(t)) dt < ∞` a.s. -/
theorem proposition_A_4 {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) → ℝ≥0 → Ω → ℝ)
    (M : Market Ω d) (K : Set (EuclideanSpace ℝ (Fin d)))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (hS : Standing P 𝓕 T W I M K U1 U2)
    (h58_1 : ∀ t ≤ T, Cond58 (U1 t)) (h58_2 : Cond58 U2) (h825 : Cond825 T U1 U2)
    (h122 : Cond122 P 𝓕 T I M K U1 U2)
    (x : ℝ) (hx : 0 < x) (τ : Triple Ω d) (hA : CondA P 𝓕 T I M K U1 U2 x τ)
    (Mt : ℝ≥0 → Ω → ℝ) (hMprog : IsStronglyProgressive 𝓕 Mt)
    (hMver : ∀ t ≤ T, Mt t =ᵐ[P] condExp (𝓕 t) P (fun ω =>
      (∫ s in Icc (0 : ℝ) T, τ.c s.toNNReal ω * deriv (U1 s.toNNReal) (τ.c s.toNNReal ω)) +
        τ.X T ω * deriv U2 (τ.X T ω)))
    (ψ : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hψ : IsLocallySquareIntegrable 𝓕 P T ψ)
    (y₀ : ℝ) (hrep : ∀ t ≤ T, ∀ᵐ ω ∂P, Mt t ω = y₀ + I ψ t ω) :
    let A : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∫ s in Icc (0 : ℝ) t, τ.c s.toNNReal ω * deriv (U1 s.toNNReal) (τ.c s.toNNReal ω)
    let μ : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d) := fun t ω =>
      theta M t ω - Matrix.toEuclideanLin (M.σ t ω).transpose (τ.π t ω)
    let lam : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d) := fun t ω =>
      -Matrix.toEuclideanLin (M.σ t ω) (μ t ω + (1 / (Mt t ω - A t ω)) • ψ t ω)
    (∀ᵐ q ∂(lebP P T), delta K (lam q.1.toNNReal q.2) +
      ((inner ℝ (lam q.1.toNNReal q.2) (τ.π q.1.toNNReal q.2) : ℝ) : EReal) = 0) ∧
    (∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => ‖lam s.toNNReal ω‖ ^ 2) (Icc (0 : ℝ) T)) ∧
    ∀ᵐ ω ∂P, ∫⁻ s in Icc (0 : ℝ) T, (delta K (lam s.toNNReal ω)).toENNReal < ⊤ := by sorry


end CvitanicKaratzas92.Optimality
