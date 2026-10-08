-- Prove2me | Theorems.Thm_ClosedLoopMFG_Converse_nu_n_converges
-- name    : ClosedLoopMFG.Converse.nu_n_converges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:29:01.485999+00:00
-- url     : https://prove2.me/theorems/195fb6ac-babc-42a5-8dc3-2f455ec5462c
-- title:
--   Section 7.1 — the empirical flow $\nu^n$ after a unilateral deviation still converges to $m$ in probability
-- statement:
--   Suppose Assumptions A and C hold, and let $(m,\Lambda^*)$ be a strong RMFE. For each $n$, let $\beta^n$ be any relaxed Markovian control. Player 1 uses $\beta^n$, and players $2,\dots,n$ use $\Lambda^{n,k}(t,x)=\Lambda^*(t,x^k)$. Let $\nu^n=\mu^n[(\beta^n,\Lambda^{n,2},\dots,\Lambda^{n,n})]$ be the empirical measure flow of any solution of this system. Then $\nu^n\to m$ in probability in $C([0,T];\mathcal P(\mathbb R^d))$, in the sense that
--   $$\lim_{n\to\infty}\mathbb P_n\big(\nu^n\notin U\big)=0\qquad\text{for every open }U\ni m.$$
--
--   A single player's deviation does not move the population limit. This is the step that lets the proof of Theorem 3.10 compare a deviating player's payoff with the mean field optimum.
--
--   **Formalization Note** The paper proves this for the particular near-optimal deviations $\beta^n$ of (7.3). Its argument (a Girsanov change of measure with $L^p$-bounded densities) does not use that choice, and the statement here is for an arbitrary sequence of relaxed Markovian controls, which contains the paper's case. Player 1 is index $0$. The game with $n+1$ players is indexed by $n$, and the claim is made for every choice of solutions.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 45, proof of Theorem 3.10 (Section 7.1), "ν^n → m in probability"

import Mathlib
import Definitions.Def_ClosedLoopMFG_Converse_Model
import Definitions.Def_ClosedLoopMFG_Converse_Game
import Definitions.Def_ClosedLoopMFG_Converse_Equilibrium

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.Converse

theorem nu_n_converges {d : ℕ} {T : ℝ≥0} (hT : 0 < T) {EA : Type}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    (A : Set EA) (lam : PR d) (b : ℝ → ClosedLoopMFG.Limit.E d → PR d → EA → ClosedLoopMFG.Limit.E d) (f : ℝ → ClosedLoopMFG.Limit.E d → PR d → EA → ℝ)
    (g : ClosedLoopMFG.Limit.E d → PR d → ℝ)
    (hA : AssumptionA T A b f g) (hC : AssumptionC T A b)
    (m : Flow d T) (Λs : ℝ → ClosedLoopMFG.Limit.E d → PA A) (hm : IsStrongRMFEWith T A lam b f g m Λs)
    (β : (n : ℕ) → ℝ → (Fin (n + 1) → ClosedLoopMFG.Limit.E d) → PA A)
    (hβ : ∀ n, IsRelaxedMarkovControl (β n))
    (S : (n : ℕ) → NSol (n + 1) d T lam
      (driftR T b (Function.update (symProfile Λs) 0 (β n)))) :
    ∀ U : Set (Flow d T), IsOpen U → m ∈ U →
      Tendsto (fun n => (S n).P {ω | (S n).μ ω ∉ U}) atTop (𝓝 0) := by sorry

end ClosedLoopMFG.Converse
