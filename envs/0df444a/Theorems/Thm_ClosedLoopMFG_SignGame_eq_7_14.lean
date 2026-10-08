-- Prove2me | Theorems.Thm_ClosedLoopMFG_SignGame_eq_7_14
-- name    : ClosedLoopMFG.SignGame.eq_7_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:24:47.083279+00:00
-- url     : https://prove2.me/theorems/65c8de1b-43a2-46cf-b266-683623497cb7
-- title:
--   (7.14) — limsup_n sup_{β∈AM_n} J^n_1(β, α^{n,2}_0, …, α^{n,n}_0) ≤ T²
-- statement:
--   In the $n$-player mean-sign game with horizon $T>0$, let players $2,\dots,n$ use the sign feedback $\alpha^{n,k}_0$ of (7.13) and let player 1 use an arbitrary Markovian control $\beta:[0,T]\times\mathbb R^n\to[-1,1]$. Then player 1's best payoff is asymptotically at most $T^2$:
--
--   $$
--   \limsup_{n\to\infty}\ \sup_{\beta\in\mathcal{AM}_n}J^n_1(\beta,\alpha^{n,2}_0,\dots,\alpha^{n,n}_0)\ \le\ T^2 .
--   $$
--
--   Together with $J^n_1(\alpha^n)\to T^2$ this gives $\varepsilon_n\to0$ in Proposition 7.2.
--
--   **Formalization Note** The $\limsup$ of a supremum is stated in its elementary form: for every $\eta>0$, for all large $n$, every Markovian deviation $\beta$ and every solution of $(\beta,\alpha^{n,2}_0,\dots,\alpha^{n,n}_0)$ give player 1 a payoff at most $T^2+\eta$. The paper prints $\alpha^{n,k}$ in (7.14) for $\alpha^{n,k}_0$. Term $n$ is the $(n+1)$-player game. Player 1 is index $0$.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 49, (7.14) (proved on p. 51)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_ClosedLoopMFG_SignGame_Model
import Definitions.Def_ClosedLoopMFG_SignGame_Game
import Definitions.Def_ClosedLoopMFG_SignGame_Example

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.SignGame

/-- (7.14), p. 49: `limsup_n sup_{β ∈ AM_n} J^n_1(β, α^{n,2}_0, …, α^{n,n}_0) ≤ T²`, stated for
every choice of solutions. Term `n` of the sequence is the `(n + 1)`-player game. -/
theorem eq_7_14 (T : ℝ≥0) (hT : 0 < T) :
    ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      ∀ β : ℝ → (Fin (n + 1) → EthierKurtz.SDEState 1) → ℝ, IsMarkovianControl T signA β →
        ∀ S' : NSol (n + 1) 1 T signLam
            (signDrift T (Function.update (signProfile (n + 1) T) 0 β)),
          signPayoff S' 0 ≤ (T : ℝ) ^ 2 + η := by sorry

end ClosedLoopMFG.SignGame
