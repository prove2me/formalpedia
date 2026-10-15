-- Prove2me | Theorems.Thm_BreakingSample_FiniteHorizon_eq_68
-- name    : BreakingSample.FiniteHorizon.eq_68
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:52.794072+00:00
-- url     : https://prove2.me/theorems/6c82dd0b-db93-4002-b74d-c875a2c255ce
-- title:
--   (68), p. 22 — 0 ≤ V⋆_h − V^{π̂⋆}_h ≤ 12H√(12Hlog(H|S||A|/δ)/N) w.p. > 1 − 2δ, provided N ≥ 48Hlog(H|S||A|/δ)
-- statement:
--   Let $(\{P_h\},\{r_h\})$ be a finite-horizon MDP on finite spaces $\mathcal S,\mathcal A$ ($\mathcal A$ nonempty) with horizon $H$ and rewards in $[0,1]$. Fix a tie-breaking rule for the dynamic program before the data are drawn, draw $N\ge1$ independent samples per triple $(s,a,h)$, and let $\widehat\pi^\star$ be the policy returned by backward dynamic programming on the empirical MDP. Let $\delta>0$ and suppose $N\ge48H\log(H|\mathcal S||\mathcal A|/\delta)$. Then with probability at least $1-2\delta$, for all $1\le h\le H$,
--   $$\mathbf 0\le V^\star_h-V^{\widehat\pi^\star}_h\le12H\sqrt{\frac{12H\log\big(H|\mathcal S||\mathcal A|/\delta\big)}{N}}\,\mathbf 1.$$
--
--   Taking the right-hand side below $\varepsilon$ gives the value part of Theorem 4.
--
--   **Formalization Note** The page says "with probability greater than $1-2\delta$"; the statement bounds the probability of the failure event by $2\delta$. Failure-event form, $N>0$, 0-based steps, tie-breaking rule fixed outside the probability.
-- source:
--   arXiv:2005.12900v8, §7.3, (68), p. 22

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_BreakingSample_FiniteHorizon_Model
import Definitions.Def_BreakingSample_FiniteHorizon_Sampling

namespace BreakingSample.FiniteHorizon

/-- (68), §7.3 (arXiv:2005.12900v8, p. 22): for the DP policy `π̂⋆` of the empirical MDP (rule `sel`, fixed
before the data), with probability greater than `1 − 2δ`, at every step
`0 ≤ V⋆_h − V^{π̂⋆}_h ≤ 12H√(12H log(H|S||A|/δ)/N) 1`, provided `N ≥ 48H log(H|S||A|/δ)`. -/
theorem eq_68 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    {H : ℕ}
    (P : Fin H → S → A → S → ℝ) (r : Fin H → S → A → ℝ) (hM : IsFHMDP P r)
    (sel : Fin H → S → (A → ℝ) → A) (hsel : IsArgmaxRule sel)
    (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : 0 < N)
    (hN48 : 48 * (H : ℝ) * Real.log ((H : ℝ) * Fintype.card S * Fintype.card A / δ) ≤ N) :
    sampleProb P N (fun x => ¬ ∀ (h : Fin H) (s : S),
      0 ≤ optValue P r h.val s - value P r (dpPolicy (empKernel x) r sel) h.val s ∧
      optValue P r h.val s - value P r (dpPolicy (empKernel x) r sel) h.val s ≤
        12 * H * Real.sqrt (12 * H * Real.log ((H : ℝ) * Fintype.card S * Fintype.card A / δ) / N))
      ≤ 2 * δ := by sorry

end BreakingSample.FiniteHorizon
