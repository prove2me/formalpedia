-- Prove2me | Theorems.Thm_CouplingHMC_Exact_eq_112_116
-- name    : CouplingHMC.Exact.eq_112_116
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:37.475605+00:00
-- url     : https://prove2.me/theorems/4e4f3ab9-7d63-424a-a546-a0db1e68bf67
-- title:
--   (112)–(116), p. 36, at h = 0 under the condition of Theorem 2.3: γT ≤ 1, LT ≤ γ/4, γℛ ≤ 1/4, aT ≥ 1, R₁ ≥ (5/2)(1+γT)ℛ
-- statement:
--   Let $T>0$, $\mathcal R\ge0$ and $L,K\in\mathbb R$ satisfy the step condition $LT^2\le\min(K/L,\tfrac14,\tfrac1{256L\mathcal R^2})$. Let $\gamma=\min(T^{-1},\mathcal R^{-1}/4)$ (with $\gamma=T^{-1}$ if $\mathcal R=0$), $a=T^{-1}$ and $R_1=\tfrac52(\mathcal R+T)$. Then
--
--   $$\gamma T\le1,\qquad LT\le\gamma/4,\qquad \gamma\mathcal R\le\tfrac14,\qquad aT\ge1,\qquad R_1\ge\tfrac52(1+\gamma T)\mathcal R.$$
--
--   These are the parameter conditions (112)–(116) on which the contraction argument for $|x-y|<2\mathcal R$ rests, read at discretization step $h=0$.
--
--   **Formalization Note.** The paper's (117), $\exp(a(R_1-2\mathcal R))\ge20$, is not included: $a(R_1-2\mathcal R)=\tfrac52+\mathcal R/(2T)$, so it fails when $\mathcal R/T<0.99$.
-- source:
--   Bou-Rabee, Eberle, Zimmer, Coupling and convergence for Hamiltonian Monte Carlo, arXiv:1805.00452v2, §5, proof of Theorem 2.4, (112)–(116), p. 36

import Mathlib
import Definitions.Def_CouplingHMC_Exact_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace CouplingHMC.Exact

/-- (112)–(116), p. 36, at `h = 0`: under the step condition of Theorem 2.3, the parameters
(28)–(30) satisfy `γT ≤ 1`, `LT ≤ γ/4`, `γℛ ≤ 1/4`, `aT ≥ 1`, `R₁ ≥ (5/2)(1 + γT)ℛ`. -/
theorem eq_112_116 (L K ℛ T : ℝ) (hT : 0 < T) (hℛ : 0 ≤ ℛ) (hTc : StepCond L K ℛ T) :
    gammaC T ℛ * T ≤ 1 ∧ L * T ≤ gammaC T ℛ / 4 ∧ gammaC T ℛ * ℛ ≤ 1 / 4 ∧
      1 ≤ aC T * T ∧ 5 / 2 * (1 + gammaC T ℛ * T) * ℛ ≤ R1C T ℛ := by sorry

end CouplingHMC.Exact
