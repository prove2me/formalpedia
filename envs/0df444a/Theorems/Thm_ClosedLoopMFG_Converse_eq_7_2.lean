-- Prove2me | Theorems.Thm_ClosedLoopMFG_Converse_eq_7_2
-- name    : ClosedLoopMFG.Converse.eq_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:29:16.219092+00:00
-- url     : https://prove2.me/theorems/9a2d64da-2654-46d0-a0bf-3f186ea284fa
-- title:
--   (7.2) — propagation of chaos for the symmetric profile $\Lambda^{n,i}(t,x)=\Lambda^*(t,x^i)$
-- statement:
--   Suppose Assumptions A and C hold, and let $(m,\Lambda^*)$ be a strong RMFE. For each $n$, let all $n$ players use the symmetric relaxed Markovian profile $\Lambda^{n,i}(t,x)=\Lambda^*(t,x^i)$. Write $\mu^n=\mu^n[\Lambda^n]$ for the empirical measure flow of any solution of the resulting $n$-player system. Then two conclusions hold.
--   1. $\mu^n\to m$ in law in $C([0,T];\mathcal P(\mathbb R^d))$, i.e. the laws of $\mu^n$ converge weakly to $\delta_m$.
--   2. For every $t\in[0,T]$ and every bounded measurable (not necessarily continuous) $\varphi:\mathbb R^d\to\mathbb R$,
--   $$\int_{\mathbb R^d}\varphi\,d\mu^n_t[\Lambda^n]\ \longrightarrow\ \int_{\mathbb R^d}\varphi\,dm_t\qquad\text{in probability}.$$
--
--   This strong form of propagation of chaos is what Assumption C buys (Lacker 2018, Theorem 2.5(2) and Remark 2.7). Convergence against discontinuous test functions lets the proof of Theorem 3.10 pass to the limit in payoffs with discontinuous feedbacks $\Lambda^*$.
--
--   **Formalization Note** The $n$-player game with $n+1$ players is indexed by $n\in\mathbb N$; a shift of index changes no limit. Both conclusions are asserted for every choice of solutions $S_n$ of the $n$-player systems: the solutions are unique in law, so this is the paper's claim. Convergence in probability of real random variables on varying spaces is stated as $\mathbb P_n(|\cdot|>\delta)\to0$ for every $\delta>0$.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 44, proof of Theorem 3.10 (Section 7.1), μ^n → m and (7.2)

import Mathlib
import Definitions.Def_ClosedLoopMFG_Converse_Model
import Definitions.Def_ClosedLoopMFG_Converse_Game
import Definitions.Def_ClosedLoopMFG_Converse_Equilibrium

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.Converse

theorem eq_7_2 {d : ℕ} {T : ℝ≥0} (hT : 0 < T) {EA : Type}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    (A : Set EA) (lam : PR d) (b : ℝ → ClosedLoopMFG.Limit.E d → PR d → EA → ClosedLoopMFG.Limit.E d) (f : ℝ → ClosedLoopMFG.Limit.E d → PR d → EA → ℝ)
    (g : ClosedLoopMFG.Limit.E d → PR d → ℝ)
    (hA : AssumptionA T A b f g) (hC : AssumptionC T A b)
    (m : Flow d T) (Λs : ℝ → ClosedLoopMFG.Limit.E d → PA A) (hm : IsStrongRMFEWith T A lam b f g m Λs)
    (S : (n : ℕ) → NSol (n + 1) d T lam (driftR T b (symProfile Λs))) :
    Tendsto (fun n => (S n).law) atTop (𝓝 (diracFlow m)) ∧
    ∀ (t : Set.Icc (0 : ℝ) T) (φ : ClosedLoopMFG.Limit.E d → ℝ), Measurable φ → (∃ C : ℝ, ∀ x, |φ x| ≤ C) →
      ∀ δ : ℝ, 0 < δ →
        Tendsto (fun n => (S n).P {ω | δ < |(∫ x, φ x ∂((S n).μ ω t).meas) -
          ∫ x, φ x ∂(m t).meas|}) atTop (𝓝 0) := by sorry

end ClosedLoopMFG.Converse
