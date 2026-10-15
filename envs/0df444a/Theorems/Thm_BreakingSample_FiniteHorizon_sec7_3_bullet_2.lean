-- Prove2me | Theorems.Thm_BreakingSample_FiniteHorizon_sec7_3_bullet_2
-- name    : BreakingSample.FiniteHorizon.sec7_3_bullet_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:58.785709+00:00
-- url     : https://prove2.me/theorems/9a3c1bdd-9ac8-4b97-958e-a95a3b1e7ca5
-- title:
--   §7.3, second bullet, pp. 21–22 — for the DP policy π̂⋆, ‖V̂^{π̂⋆}_h − V^{π̂⋆}_h‖∞ ≤ 6H√(12Hlog(H|S||A|/δ)/N) w.p. ≥ 1 − δ
-- statement:
--   Let $(\{P_h\},\{r_h\})$ be a finite-horizon MDP on finite spaces $\mathcal S,\mathcal A$ ($\mathcal A$ nonempty) with horizon $H$ and rewards in $[0,1]$. Fix a tie-breaking rule for the dynamic program before the data are drawn, draw $N\ge1$ independent samples per triple $(s,a,h)$, and let $\widehat\pi^\star$ be the policy returned by backward dynamic programming on the empirical MDP $\widehat{\mathcal M}=(\{\widehat P_h\},\{r_h\})$. Let $\delta>0$ and suppose
--   $$N\ge48H\log\Big(\frac{H|\mathcal S||\mathcal A|}{\delta}\Big).$$
--   Then with probability at least $1-\delta$, for all $1\le h\le H$,
--   $$\big\|\widehat V^{\widehat\pi^\star}_h-V^{\widehat\pi^\star}_h\big\|_\infty\le6H\sqrt{\frac{12H\log\big(H|\mathcal S||\mathcal A|/\delta\big)}{N}},$$
--   where $V^{\widehat\pi^\star}_h$ and $\widehat V^{\widehat\pi^\star}_h$ are the values of $\widehat\pi^\star$ in the true and in the empirical MDP.
--
--   This is the second of the two error terms of the decomposition (65). The planner's policy depends on the data, but its step-$h$ rule depends only on $\widehat P_h,\dots,\widehat P_H$, which is what makes the concentration of (66) available for it.
--
--   **Formalization Note** The page leaves the sample-size condition of Lemma 9 implicit here ($N\ge12H\beta_1$ with $\beta_1=4\log(H|\mathcal S||\mathcal A|/\delta)$, stated as the proviso of (68)); it is written out as a hypothesis. The planner is greedy for the empirical $Q^\star$ with the fixed tie-breaking rule. Failure-event form of the probability, $N>0$, 0-based steps.
-- source:
--   arXiv:2005.12900v8, §7.3, second bullet, pp. 21–22

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_BreakingSample_FiniteHorizon_Model
import Definitions.Def_BreakingSample_FiniteHorizon_Sampling

namespace BreakingSample.FiniteHorizon

/-- §7.3, second bullet (arXiv:2005.12900v8, pp. 21–22): for the DP policy `π̂⋆` of the empirical MDP (run
with the tie-breaking rule `sel`, fixed before the data), with probability at least `1 − δ`,
`‖V̂^{π̂⋆}_h − V^{π̂⋆}_h‖∞ ≤ 6H√(12H log(H|S||A|/δ)/N)` at every step, provided
`N ≥ 48H log(H|S||A|/δ)` (Lemma 9's condition `N ≥ 12Hβ₁`, left implicit on the page). -/
theorem sec7_3_bullet_2 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A] {H : ℕ}
    (P : Fin H → S → A → S → ℝ) (r : Fin H → S → A → ℝ) (hM : IsFHMDP P r)
    (sel : Fin H → S → (A → ℝ) → A) (hsel : IsArgmaxRule sel)
    (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : 0 < N)
    (hN48 : 48 * (H : ℝ) * Real.log ((H : ℝ) * Fintype.card S * Fintype.card A / δ) ≤ N) :
    sampleProb P N (fun x => ¬ ∀ h : Fin H,
      ‖value (empKernel x) r (dpPolicy (empKernel x) r sel) h.val -
          value P r (dpPolicy (empKernel x) r sel) h.val‖ ≤
        6 * H * Real.sqrt (12 * H * Real.log ((H : ℝ) * Fintype.card S * Fintype.card A / δ) / N))
      ≤ δ := by sorry

end BreakingSample.FiniteHorizon
