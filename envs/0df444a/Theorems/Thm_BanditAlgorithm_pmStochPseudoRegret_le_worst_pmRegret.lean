-- Prove2me | Theorems.Thm_BanditAlgorithm_pmStochPseudoRegret_le_worst_pmRegret
-- name    : BanditAlgorithm.pmStochPseudoRegret_le_worst_pmRegret
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T18:44:45.927313+00:00
-- url     : https://prove2.me/theorems/026410cf-50cd-47e5-9abd-e2107db1e9c5
-- title:
--   Stochastic partial-monitoring regret is bounded by worst-case regret
-- statement:
--   Fix a finite partial-monitoring game, a policy, a horizon $n$, an outcome distribution $u$, and a comparator action $a$. Let $R_n(\pi,u;a)$ be the expected stochastic pseudo-regret when the outcomes are sampled independently from $u$. Then
--
--   $$
--   R_n(\pi,u;a)\le \max_{i_{1:n}} R_n(\pi,i_{1:n}),
--   $$
--
--   where the maximum on the right is the policy’s regret over deterministic outcome sequences, with its usual best fixed-action comparator.
--
--   This is the finite-mixture/Yao bridge used when a stochastic two-environment lower bound is converted into a lower bound for adversarial minimax regret. The stochastic experiment is a probability mixture of the deterministic experiments, and regret against the fixed action $a$ is bounded pointwise by regret against the best fixed action.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (Cambridge UP, 2020), Theorem 37.12 Step 3, printed p. 491, the display beginning R_n(pi,u_a)+R_n(pi,u_b), together with the adversarial minimax definition in Section 37.2, printed p. 483. The bridge is the finite-mixture interpretation of the stochastic environments used there.

import Definitions.Def_PartialMonitoringStochastic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

theorem BanditAlgorithm.pmStochPseudoRegret_le_worst_pmRegret
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d))
    (n : ℕ) (a : Fin k) :
    pmStochPseudoRegret G π u hu n a ≤
      ⨆ i : Fin n → Fin d, pmRegret G π n i := by
  sorry
