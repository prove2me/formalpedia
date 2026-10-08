-- Prove2me | Theorems.Thm_CvitanicKaratzas92_Optimality_theorem_7_4
-- name    : CvitanicKaratzas92.Optimality.theorem_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:11:27.284228+00:00
-- url     : https://prove2.me/theorems/3d04496a-6df8-4692-8a25-5fda2b7d31ff
-- title:
--   Theorem 7.4 — the unconstrained problem is solved by $(\pi_0,c_0)$ with $X(T)=\xi_0$
-- statement:
--   Under the standing assumptions and Assumption 7.1 ($\mathcal X_0(y)<\infty$ for every $y>0$), let $x>0$, $y=\mathcal Y_0(x)$, and let $\xi_0=I_2(yH_0(T))$, $c_0(t)=I_1(t,yH_0(t))$ be as in (7.2)–(7.3). Then there exists a portfolio process $\pi_0$ such that
--   $$(\pi_0,c_0)\in\mathcal A_0'(x),\qquad X^{x,\pi_0,c_0}(T)=\xi_0\ \text{a.s.},\qquad V_0(x)=J(x;\pi_0,c_0).$$
--
--   This is the classical solution of the unconstrained problem; Section 8 applies it in every auxiliary market $\mathcal M_\nu$ to obtain $c_\nu,\xi_\nu,X_\nu$.
--
--   **Formalization Note** $\mathcal Y_0(x)$ is a binder $y>0$ with $\mathcal X_0(y)=x$. The value $V_0(x)$ and $J$ are extended reals.
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), p. 776, Theorem 7.4

import Mathlib
import Definitions.Def_CvitanicKaratzas92_Optimality_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Optimality

/-- Cvitanić–Karatzas (1992), Theorem 7.4, p. 776. Under Assumption 7.1, with `y = 𝒴₀(x)` and
`ξ₀`, `c₀` as in (7.2)–(7.3), there is a portfolio `π₀` with `(π₀, c₀) ∈ 𝒜₀'(x)`,
`X^{x,π₀,c₀}(T) = ξ₀` a.s. and `V₀(x) = J(x; π₀, c₀)`. -/
theorem theorem_7_4 {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) → ℝ≥0 → Ω → ℝ)
    (M : Market Ω d) (K : Set (EuclideanSpace ℝ (Fin d)))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (hS : Standing P 𝓕 T W I M K U1 U2)
    (h71 : ∀ y : ℝ, 0 < y → calX0 P T I M U1 U2 y < ⊤)
    (x : ℝ) (hx : 0 < x) (y : ℝ) (hy : 0 < y)
    (hxy : calX0 P T I M U1 U2 y = ENNReal.ofReal x) :
    ∃ (π₀ : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (X : ℝ≥0 → Ω → ℝ),
      ⟨π₀, c0 I M U1 y, X⟩ ∈ A0' P 𝓕 T I M U1 U2 x ∧
      (∀ᵐ ω ∂P, X T ω = xi0 T I M U2 y ω) ∧
      V0 P 𝓕 T I M U1 U2 x = J P T U1 U2 ⟨π₀, c0 I M U1 y, X⟩ := by sorry


end CvitanicKaratzas92.Optimality
