-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_span_le_gain_mul_diameter
-- name    : BanditAlgorithm.mdp_span_le_gain_mul_diameter
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T04:51:03.348974+00:00
-- url     : https://prove2.me/theorems/c74fb3fa-aff3-43b9-9de6-5f625be86486
-- title:
--   Span of the bias is at most gain $\times$ diameter
-- statement:
--   Let $M$ be a finite MDP of finite diameter and let $(\rho, v)$ satisfy the Bellman optimality inequality
--
--   $$r_a(s) + \langle P_a(s), v\rangle \;\le\; \rho + v(s) \qquad \text{for all } s, a,$$
--
--   with $v$ bounded and $\rho \ge 0$. Then for all states $s, s'$,
--
--   $$v(s) - v(s') \;\le\; \rho\, D(M), \qquad \text{that is} \qquad \mathrm{span}(v) \le \rho\, D(M).$$
--
--   This is Lemma 38.3 of Lattimore and Szepesvári, whose proof is left to their Exercise 38.13, in the sharp form $\mathrm{span}(v) \le (\rho^{*} - \min_{s,a} r_a(s)) D(M)$ specialised to rewards in $[0,1]$. Since a solution of the Bellman optimality equation has $\rho = \rho^{*} \le 1$, it gives $\mathrm{span}(v) \le D(M)$, which is how the lemma is used: in Step 2 of the proof of Theorem 38.6 the boundary term $v_k(S_{\tau_{k+1}}) - v_k(S_{\tau_k})$ of each phase of UCRL2 is bounded by the span of the optimistic value function, hence by the diameter, and the phase count multiplies it.
--
--   The proof is the per-policy inequality $v(\mathrm{tgt}) - v(\mathrm{src}) \le \rho\, \mathbb{E}^{f}[\tau_{\mathrm{tgt}} - 1 \mid S_1 = \mathrm{src}]$ evaluated at a policy minimising the travel time from $s'$ to $s$ — the minimum is attained because there are finitely many memoryless deterministic policies — followed by the observation that this minimum is one of the terms of the maximum defining $D(M)$. The finiteness of the diameter is what makes the travel time of the minimising policy finite, and hence the argument applicable.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Lemma 38.3 and Exercise 38.13 (Section 38.2), used in Step 2 of the proof of Theorem 38.6; Jaksch, Ortner & Auer, Near-optimal Regret Bounds for Reinforcement Learning, JMLR 11 (2010), Section 4.3.1.

import Definitions.Def_FiniteMDPLearning
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_span_le_gain_mul_diameter {S A : ℕ} (M : FiniteMDP S A)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (v : Fin S → ℝ) (lo hi : ℝ) (hv : ∀ s, v s ∈ Set.Icc lo hi)
    (hbell : ∀ s a, M.r s a + ∑ s', (M.P s a s' : ℝ) * v s' ≤ ρ + v s)
    (hD : mdpDiameterENN M ≠ ⊤) (s s' : Fin S) :
    v s - v s' ≤ ρ * mdpDiameter M := by
  sorry
