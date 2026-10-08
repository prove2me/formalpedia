-- Prove2me | Theorems.Thm_CvitanicKaratzas92_Optimality_lemma_7_2
-- name    : CvitanicKaratzas92.Optimality.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:51:51.902984+00:00
-- url     : https://prove2.me/theorems/01418d5f-f015-468b-a941-9549492130e3
-- title:
--   Lemma 7.2 — $c_0,\xi_0$ exhaust the budget, have integrable utility losses, and dominate every unconstrained policy
-- statement:
--   Under the standing assumptions, suppose Assumption 7.1: the expectation
--   $$\mathcal X_0(y)=E\Big[\int_0^TH_0(t)I_1(t,yH_0(t))\,dt+H_0(T)I_2(yH_0(T))\Big]$$
--   is finite for every $y\in(0,\infty)$. Let $x>0$, let $y=\mathcal Y_0(x)$ be the number with $\mathcal X_0(y)=x$, and set $\xi_0=I_2(yH_0(T))$, $c_0(t)=I_1(t,yH_0(t))$, $0\le t\le T$. Then
--   $$E\Big[\int_0^TH_0(t)c_0(t)\,dt+H_0(T)\xi_0\Big]=x, \tag{7.4}$$
--   $$E\int_0^TU_1^-(t,c_0(t))\,dt+EU_2^-(\xi_0)<\infty, \tag{7.5}$$
--   $$J(x;\pi,c)\le E\Big[\int_0^TU_1(t,c_0(t))\,dt+U_2(\xi_0)\Big]\quad\forall(\pi,c)\in\mathcal A_0'(x). \tag{7.6}$$
--
--   Together with Proposition 7.3, this solves the unconstrained problem (6.3); the same argument in each auxiliary market $\mathcal M_\nu$ underlies Section 8.
--
--   **Formalization Note** $\mathcal Y_0(x)$ is represented by a binder $y>0$ with $\mathcal X_0(y)=x$. The right-hand side of (7.6) is an extended-real expectation (positive minus negative parts).
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), p. 774, Assumption 7.1, (7.1)–(7.3), Lemma 7.2

import Mathlib
import Definitions.Def_CvitanicKaratzas92_Optimality_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Optimality

/-- Cvitanić–Karatzas (1992), Lemma 7.2, p. 774. Under Assumption 7.1 (`𝒳₀(y) < ∞` for every
`y > 0`), with `y = 𝒴₀(x)` (i.e. `𝒳₀(y) = x`), `c₀(t) = I₁(t, yH₀(t))` and `ξ₀ = I₂(yH₀(T))`:
(7.4) `E[∫₀ᵀ H₀(t)c₀(t) dt + H₀(T)ξ₀] = x`; (7.5) `E∫₀ᵀ U₁⁻(t, c₀(t)) dt + EU₂⁻(ξ₀) < ∞`;
(7.6) `J(x; π, c) ≤ E[∫₀ᵀ U₁(t, c₀(t)) dt + U₂(ξ₀)]` for every `(π, c) ∈ 𝒜₀'(x)`. -/
theorem lemma_7_2 {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) → ℝ≥0 → Ω → ℝ)
    (M : Market Ω d) (K : Set (EuclideanSpace ℝ (Fin d)))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (hS : Standing P 𝓕 T W I M K U1 U2)
    (h71 : ∀ y : ℝ, 0 < y → calX0 P T I M U1 U2 y < ⊤)
    (x : ℝ) (hx : 0 < x) (y : ℝ) (hy : 0 < y)
    (hxy : calX0 P T I M U1 U2 y = ENNReal.ofReal x) :
    (∫⁻ ω, ((∫⁻ s in Icc (0 : ℝ) T,
        ENNReal.ofReal (H0 I M s.toNNReal ω * c0 I M U1 y s.toNNReal ω)) +
      ENNReal.ofReal (H0 I M T ω * xi0 T I M U2 y ω)) ∂P = ENNReal.ofReal x) ∧
    utilNeg P T U1 U2 (c0 I M U1 y) (xi0 T I M U2 y) < ⊤ ∧
    ∀ τ ∈ A0' P 𝓕 T I M U1 U2 x,
      J P T U1 U2 τ ≤ expUtil P T U1 U2 (c0 I M U1 y) (xi0 T I M U2 y) := by sorry


end CvitanicKaratzas92.Optimality
