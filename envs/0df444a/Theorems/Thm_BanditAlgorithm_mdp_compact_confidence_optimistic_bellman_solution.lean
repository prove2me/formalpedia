-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_compact_confidence_optimistic_bellman_solution
-- name    : BanditAlgorithm.mdp_compact_confidence_optimistic_bellman_solution
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T16:33:10.301171+00:00
-- url     : https://prove2.me/theorems/c3a3d84d-bc18-4d7d-92ba-470d30fa107b
-- title:
--   Optimistic Bellman solution over compact confidence sets
-- statement:
--   Fix $S$ states and $A$ actions, a reward function $r_a(s)\in[0,1]$, and for each state-action pair a nonempty **compact** set $\mathcal C_{s,a}$ of probability vectors on the state space. Suppose some genuine finite MDP $M$ with reward function $r$ and finite diameter $D(M)$ has all of its transition rows in the confidence sets, $P_a(s)\in\mathcal C_{s,a}$. Then the average-reward Bellman optimality equation of the extended MDP has a solution: there are a gain $\rho\in[0,1]$, a value function $v$, an action map $f$ and optimistic rows $q(s)\in\mathcal C_{s,f(s)}$ with
--
--   $$
--   \mathrm{span}(v)\le \rho\, D(M),\qquad
--   r_a(s)+\langle p, v\rangle\;\le\;\rho+v(s)\ \ \text{for all }a\text{ and all }p\in\mathcal C_{s,a},\qquad
--   \rho+v(s)=r_{f(s)}(s)+\langle q(s), v\rangle,
--   $$
--
--   and $\rho$ is *optimistic*: $\rho^{*}(M)\le\rho$.
--
--   This is the guarantee that extended value iteration in UCRL2 converges to a solution of the optimality equation of the extended MDP, together with the two properties the regret analysis consumes: optimism, and the bound on the span of the optimistic value function by the diameter of the true MDP. The extended MDP is not a finite MDP, since its action set — the pairs $(a,p)$ with $p$ in a confidence set — is a continuum; the hypotheses replace finiteness of the action set by compactness of the confidence sets.
--
--   The proof is the vanishing-discount argument. For $\gamma<1$ let $V_\gamma$ solve the discounted extended Bellman equation and put $\rho_\gamma=(1-\gamma)\max_s V_\gamma(s)\in[0,1]$. Splitting $\langle p, V_\gamma\rangle$ as $\gamma\langle p, V_\gamma\rangle+(1-\gamma)\langle p, V_\gamma\rangle$ shows that $(\rho_\gamma, V_\gamma)$ solves the average-reward Bellman *inequality* for every member of the confidence region — in particular for the genuine MDP $M$, whence $\mathrm{span}(V_\gamma)\le\rho_\gamma D(M)\le D(M)$ uniformly in $\gamma$. So the recentred functions $V_\gamma - V_\gamma(s_0)$ range in the compact cube $[-D,D]^{\mathcal S}$, the gains range in $[0,1]$ and the optimistic rows range in the compact confidence sets, while the maximising actions range over a finite set. Along a subsequence $\gamma_k\uparrow 1$ the action map is therefore a fixed $f$ and everything else converges; the inequality persists in the limit, and the defect in the greedy equality — which equals $(1-\gamma)\big(\max_s V_\gamma(s)-\langle q(s),V_\gamma\rangle\big)$ and so lies between $0$ and $(1-\gamma)D(M)$ — vanishes. Optimism is then the verification half of Theorem 38.2 applied to $M$, whose rows lie in the confidence sets.
--
--   Finiteness of the diameter of the true MDP is exactly what makes the limit exist: without a uniform span bound the recentred discounted value functions need not be bounded.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Section 38.5 and Theorem 38.2 (Section 38.2), used in the proof of Theorem 38.6; Jaksch, Ortner & Auer, Near-optimal Regret Bounds for Reinforcement Learning, JMLR 11 (2010), Section 3.1 and Theorem 7.

import Definitions.Def_FiniteMDPLearning
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_compact_confidence_optimistic_bellman_solution
    {S A : ℕ} (hS : 0 < S) (hA : 0 < A)
    (r : Fin S → Fin A → ℝ) (hr : ∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1)
    (C : Fin S → Fin A → Set (Fin S → ℝ)) (hCne : ∀ s a, (C s a).Nonempty)
    (hCcomp : ∀ s a, IsCompact (C s a))
    (hCprob : ∀ s a, ∀ p ∈ C s a, (∀ s', 0 ≤ p s') ∧ ∑ s', p s' = 1)
    (M : FiniteMDP S A) (hMr : M.r = r) (hMD : mdpDiameterENN M ≠ ⊤)
    (hMC : ∀ s a, (fun s' ↦ ((M.P s a s' : ℝ))) ∈ C s a) :
    ∃ (ρ : ℝ) (v : Fin S → ℝ) (f : Fin S → Fin A) (q : Fin S → Fin S → ℝ),
      0 ≤ ρ ∧ ρ ≤ 1 ∧
      (∀ s s', v s - v s' ≤ ρ * mdpDiameter M) ∧
      (∀ s a, ∀ p ∈ C s a, r s a + ∑ s', p s' * v s' ≤ ρ + v s) ∧
      (∀ s, q s ∈ C s (f s)) ∧
      (∀ s, ρ + v s = r s (f s) + ∑ s', q s s' * v s') ∧
      mdpOptimalGain M ≤ ρ := by
  sorry
