-- Prove2me | Theorems.Thm_CondatPD_PPA_A_maximal_monotone
-- name    : CondatPD.PPA.A_maximal_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:35:59.526018+00:00
-- url     : https://prove2.me/theorems/d8dbfa54-ac94-4b50-9d1c-da03b8fe947a
-- title:
--   §4, proof of Theorem 3.1, p. 11 — the operator A of (22) is maximally monotone in 𝒵_I
-- statement:
--   Let $\mathcal X,\mathcal Y$ be real Hilbert spaces, $L:\mathcal X\to\mathcal Y$ bounded linear, $G\in\Gamma_0(\mathcal X)$ and $H\in\Gamma_0(\mathcal Y)$. On the Hilbert space $\mathcal Z_I=\mathcal X\times\mathcal Y$ with $\langle (x,y),(x',y')\rangle_I=\langle x,x'\rangle+\langle y,y'\rangle$, the set-valued operator
--   $$A(x,y)=\big(\partial G(x)+L^*y\big)\times\big(-Lx+\partial H^*(y)\big)$$
--   is maximally monotone.
--
--   In the paper, $A$ is the sum of the maximally monotone operator $(x,y)\mapsto\partial G(x)\times\partial H^*(y)$ and the skew operator $(x,y)\mapsto(L^*y,-Lx)$. Its maximal monotonicity, transferred to $P^{-1}\circ A$ in $\mathcal Z_P$, is one of the conditions of Lemma 4.2 checked for Theorem 3.2.
--
--   **Formalization Note** $\mathcal Z_I$ is `WithLp 2 (X × Y)`; maximal monotonicity is the published `IsMaximalMonotone` (monotone, with no proper monotone extension of the graph). $H^*$ is the published `EReal` conjugate `MoreauProx.Characterization.conj`.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 11, §4, proof of Theorem 3.1 for Algorithm 3.1, first bullet; A from (22), p. 10

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_CondatPD_PPA_Setting

namespace CondatPD.PPA

theorem A_maximal_monotone {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (G : X → EReal) (H : Y → EReal) (L : X →L[ℝ] Y)
    (hG : ThreeOpSplitting.ConvexRates.IsProperClosedConvex G)
    (hH : ThreeOpSplitting.ConvexRates.IsProperClosedConvex H) :
    ThreeOpSplitting.Convergence.IsMaximalMonotone (opA G H L) := by sorry

end CondatPD.PPA
