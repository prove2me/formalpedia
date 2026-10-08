-- Prove2me | Theorems.Thm_ClosedLoopMFG_SignGame_payoff_tendsto_T_sq
-- name    : ClosedLoopMFG.SignGame.payoff_tendsto_T_sq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:24:26.617017+00:00
-- url     : https://prove2.me/theorems/101e5b5f-732a-4544-8fca-3abe8efd6112
-- title:
--   Proof of Proposition 7.2, p. 49 — under the sign feedback, J^n_1(α^n) = E|μ̄^n_T|² → T²
-- statement:
--   Consider the $n$-player mean-sign game (Section 7.3) with time horizon $T>0$, in which every player uses the sign feedback $\alpha^{n,i}_0(t,x)=\operatorname{sgn}\big(\tfrac1n\sum_k x_k\big)\mathbf 1_{(0,T]}(t)$ of (7.13). Let $X^1,\dots,X^n$ be the states on any solution and $\overline\mu^n_t=\frac1n\sum_kX^k_t$ the mean process. Then player 1's payoff satisfies
--
--   $$
--   J^n_1(\alpha^{n,1}_0,\dots,\alpha^{n,n}_0)=\mathbb E\big[X^1_T\,\overline\mu^n_T\big]=\mathbb E\big[|\overline\mu^n_T|^2\big]\ \longrightarrow\ T^2\qquad(n\to\infty).
--   $$
--
--   This is the first half of the reduction in the proof of Proposition 7.2: it identifies the limit of the equilibrium payoff, so that $\varepsilon_n\to0$ follows from the upper bound (7.14).
--
--   **Formalization Note** Term $n$ of the sequence is the $(n+1)$-player game, so the $\frac1n$ of the paper is $\frac1{n+1}$ here, both in the controls and in the mean; a shift of index changes no limit. The statement holds for every choice of solutions (all have the same law). The first equality $J^n_1=\mathbb E[X^1_T\overline\mu^n_T]$ is definitional ($f\equiv0$); the stated identity is $J^n_1=\mathbb E[|\overline\mu^n_T|^2]$, which the paper obtains by symmetry. Player 1 is index $0$.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 49, proof of Proposition 7.2 (Section 7.4)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_ClosedLoopMFG_SignGame_Model
import Definitions.Def_ClosedLoopMFG_SignGame_Game
import Definitions.Def_ClosedLoopMFG_SignGame_Example

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.SignGame

/-- Proof of Proposition 7.2 (Section 7.4), p. 49: under the sign feedback profile, player 1's
payoff equals `E[|μ̄^n_T|²]` and converges to `T²`. Term `n` of the sequence is the
`(n + 1)`-player game. -/
theorem payoff_tendsto_T_sq (T : ℝ≥0) (hT : 0 < T)
    (S : (n : ℕ) → NSol (n + 1) 1 T signLam (signDrift T (signProfile (n + 1) T))) :
    (∀ n, signPayoff (S n) 0 = ∫ ω, (meanPath (S n) ω (tend T)) ^ 2 ∂(S n).P) ∧
    Tendsto (fun n => signPayoff (S n) 0) atTop (𝓝 ((T : ℝ) ^ 2)) := by sorry

end ClosedLoopMFG.SignGame
