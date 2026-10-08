-- Prove2me | Theorems.Thm_CondatPD_FinDim_opP_stepT_eq_of_solution
-- name    : CondatPD.FinDim.opP_stepT_eq_of_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:40:29.462506+00:00
-- url     : https://prove2.me/theorems/7ae9d7b4-d8f9-499c-bcfb-94f79e73b97b
-- title:
--   §4, proof of Theorem 3.3, pp. 12–13, (41)–(42) — on solutions of (6) with F = 0, P T(z) = P z
-- statement:
--   Let $\mathcal X,\mathcal Y$ be real Hilbert spaces, $G\in\Gamma_0(\mathcal X)$, $H\in\Gamma_0(\mathcal Y)$, $L:\mathcal X\to\mathcal Y$ bounded linear, $\tau>0$, $\sigma>0$ with $\sigma\tau\|L\|^2\le1$, and let $\mathrm{prox}_{\tau G}$, $\mathrm{prox}_{\sigma H^*}$ be the proximity operators. Let $T$ be the operator of the proof of Theorem 3.3 and $P$ the operator (20). If $z=(x,y)$ solves (6) with $F=0$, i.e.
--   $$0\in\partial G(x)+L^*y,\qquad 0\in-Lx+\partial H^*(y),$$
--   then
--   $$P\,T(z)=Pz .$$
--
--   In the paper's language, $z\in\operatorname{zer}(A)$ implies $PT(z)=Pz$, so $Sz$ is a fixed point of $T'=S\circ T$ and $\operatorname{fix}(T')\neq\emptyset$.
--
--   **Formalization Note** With $F=0$, $z\in\operatorname{zer}(A)$ is exactly "$z$ solves (6)". The step via [32, Corollary 18.17] (a positive self-adjoint $P$ with $\langle w,Pw\rangle=0$ has $Pw=0$) is part of the claim. Finite dimension is not assumed.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), pp. 12–13, §4, proof of Theorem 3.3 for Algorithm 3.1, (41)–(42)

import Mathlib
import Definitions.Def_CondatPD_FinDim_Setting

open InnerProductSpace

namespace CondatPD.FinDim

/-- Proof of Theorem 3.3, (41)–(42) (pp. 12–13): if `F = 0` and `z` solves (6), i.e.
`z ∈ zer(A)`, then `P T(z) = P z`. -/
theorem opP_stepT_eq_of_solution {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (G : X → EReal) (H : Y → EReal) (L : X →L[ℝ] Y)
    (hG : ThreeOpSplitting.ConvexRates.IsProperClosedConvex G)
    (hH : ThreeOpSplitting.ConvexRates.IsProperClosedConvex H)
    (τ σ : ℝ) (hτ : 0 < τ) (hσ : 0 < σ)
    (PG : X → X) (PH : Y → Y)
    (hPG : ThreeOpSplitting.ConvexRates.IsProx τ G PG)
    (hPH : ThreeOpSplitting.ConvexRates.IsProx σ (conj H) PH)
    (hi : σ * τ * ‖L‖ ^ 2 ≤ 1) :
    ∀ (x : X) (y : Y), IsPDSolution 0 G H L x y →
      opP τ σ L (stepT PG PH τ σ L (x, y)) = opP τ σ L (x, y) := by sorry

end CondatPD.FinDim
