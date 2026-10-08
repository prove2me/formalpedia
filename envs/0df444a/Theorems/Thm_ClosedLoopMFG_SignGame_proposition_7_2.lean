-- Prove2me | Theorems.Thm_ClosedLoopMFG_SignGame_proposition_7_2
-- name    : ClosedLoopMFG.SignGame.proposition_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:24:26.212186+00:00
-- url     : https://prove2.me/theorems/7bbd46ad-da97-438a-8d52-85fc60c79e2a
-- title:
--   Proposition 7.2 — in the mean-sign game the sign feedback is a Markovian ε_n-Nash equilibrium with ε_n → 0, and the mean converges in law to ½δ_{H⁺_0}+½δ_{H⁻_0}
-- statement:
--   Consider the $n$-player mean-sign game of Section 7.3: $d=1$, horizon $T>0$, drift $b(t,x,m,a)=a$, no running reward, terminal reward $g(x,m)=x\,\overline m$, controls in $A=[-1,1]$ and initial law $\delta_0$. Let $\alpha^n=(\alpha^{n,1}_0,\dots,\alpha^{n,n}_0)$ be the profile in which every player uses the sign feedback of (7.13) with $t_0=0$,
--
--   $$
--   \alpha^{n,i}_0(t,x)=\operatorname{sgn}\Big(\frac1n\sum_{k=1}^nx_k\Big)\mathbf 1_{(0,T]}(t).
--   $$
--
--   Then:
--
--   1. the $n$-player system under $\alpha^n$ has a solution for every $n$;
--   2. there are $\varepsilon_n\ge0$ with $\varepsilon_n\to0$ such that $\alpha^n$ is a Markovian $\varepsilon_n$-Nash equilibrium for each $n$;
--   3. the law of the mean process $(\overline\mu^n_t[\alpha^n])_{t\in[0,T]}$, $\overline\mu^n_t=\frac1n\sum_kX^k_t$, converges weakly on $C([0,T];\mathbb R)$:
--
--   $$
--   \mathcal L\big((\overline\mu^n_t[\alpha^n])_{t\in[0,T]}\big)\ \Longrightarrow\ \tfrac12\delta_{H^+_0}+\tfrac12\delta_{H^-_0},\qquad H^\pm_0(t)=\pm t .
--   $$
--
--   The example shows explicit symmetric Markovian approximate equilibria whose population mean converges to a random limit: by the vanishing noise in the mean, the equal mixture of the two strong equilibria with drift $\pm1$ is selected among the infinitely many solutions of the limiting ODE.
--
--   **Formalization Note** Term $n$ of each sequence is the $(n+1)$-player game, so the $\frac1n$ of the paper is $\frac1{n+1}$ in both the controls and the mean; a shift of index changes no limit. Clause 1 is added so that clause 2, which quantifies over solutions, cannot hold vacuously; the paper takes existence for granted (Section 2.1, p. 6). Clause 3 holds for every choice of solutions (they are unique in law). The paper's "law of the $\mathcal C^d$-valued random variable" with $d=1$ is a law on $C([0,T];\mathbb R)$. The payoffs are Bochner integrals of the unbounded $X^i_T\,\overline\mu^n_T$; these are integrable on every solution (the drift is bounded and $X^i_0=0$), so the junk value $0$ never enters. The paper proves the last claim by citing its reference [57]; it is stated here as part of the proposition.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 49, Proposition 7.2

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_ClosedLoopMFG_SignGame_Model
import Definitions.Def_ClosedLoopMFG_SignGame_Game
import Definitions.Def_ClosedLoopMFG_SignGame_Example

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.SignGame

/-- Proposition 7.2, p. 49. The sign feedback profile `α^n` ((7.13) with `t₀ = 0`) has
solutions, is a Markovian `ε_n`-Nash equilibrium with `ε_n ≥ 0`, `ε_n → 0`, and the law of the
mean process `(μ̄^n_t)_{t ∈ [0, T]}` converges to `½δ_{H⁺_0} + ½δ_{H⁻_0}`. Term `n` of each
sequence is the `(n + 1)`-player game. -/
theorem proposition_7_2 (T : ℝ≥0) (hT : 0 < T) :
    (∀ n : ℕ, Nonempty (NSol (n + 1) 1 T signLam (signDrift T (signProfile (n + 1) T)))) ∧
    (∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ n, IsSignMarkovianNash T (ε n) (signProfile (n + 1) T)) ∧
    ∀ S : (n : ℕ) → NSol (n + 1) 1 T signLam (signDrift T (signProfile (n + 1) T)),
      Tendsto (fun n => meanLaw (S n)) atTop (𝓝 (halfMix T)) := by sorry

end ClosedLoopMFG.SignGame
