-- Prove2me | Theorems.Thm_BreakingSample_FiniteHorizon_eq_65
-- name    : BreakingSample.FiniteHorizon.eq_65
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:58.989992+00:00
-- url     : https://prove2.me/theorems/f685d809-e70a-41ac-b71b-3957fa2c0933
-- title:
--   (65), p. 21 — V⋆_h − V^{π̂⋆}_h = (V̂^{π̂⋆}_h − V^{π̂⋆}_h) + (V̂^{π⋆}_h − V̂^{π̂⋆}_h) + (V⋆_h − V̂^{π⋆}_h) ≤ (V̂^{π̂⋆}_h − V^{π̂⋆}_h) + (V^{π⋆}_h − V̂^{π⋆}_h)
-- statement:
--   Let $(\{P_h\},\{r_h\})$ be a finite-horizon MDP with horizon $H$ and rewards in $[0,1]$ on finite spaces $\mathcal S,\mathcal A$ ($\mathcal A$ nonempty), and let $\{\widehat P_h\}$ be any family of transition kernels on the same spaces. Let $\pi^\star$ be an optimal policy of the MDP, and let $\widehat\pi^\star$ be the policy returned by backward dynamic programming (with any tie-breaking rule) on $(\{\widehat P_h\},\{r_h\})$. Write $V^\pi_h$ and $\widehat V^\pi_h$ for the values of $\pi$ under $\{P_h\}$ and $\{\widehat P_h\}$. Then for every step $h$, entrywise,
--   $$\begin{aligned}V^\star_h-V^{\widehat\pi^\star}_h&=\big(\widehat V^{\widehat\pi^\star}_h-V^{\widehat\pi^\star}_h\big)+\big(\widehat V^{\pi^\star}_h-\widehat V^{\widehat\pi^\star}_h\big)+\big(V^\star_h-\widehat V^{\pi^\star}_h\big)\\&\le\big(\widehat V^{\widehat\pi^\star}_h-V^{\widehat\pi^\star}_h\big)+\big(V^{\pi^\star}_h-\widehat V^{\pi^\star}_h\big).\end{aligned}$$
--
--   This decomposition reduces the suboptimality of the planner to two policy-evaluation errors, one for a fixed policy and one for the planner's own policy.
--
--   **Formalization Note** The page applies the decomposition to the empirical kernels; any family of transition kernels is allowed here. Steps are 0-based.
-- source:
--   arXiv:2005.12900v8, §7.3, (65), p. 21

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_BreakingSample_FiniteHorizon_Model

namespace BreakingSample.FiniteHorizon

open FoundationsML.ReinforcementLearning

/-- The decomposition (65), §7.3 (arXiv:2005.12900v8, p. 21). Let `π⋆` be an optimal policy of `(P, r)` and
`π̂⋆` the DP policy (rule `sel`) of the MDP `(P̂, r)`, for any family of transition kernels `P̂` (the empirical
kernels of (6) are one). Then at every step and state
`V⋆_h − V^{π̂⋆}_h = (V̂^{π̂⋆}_h − V^{π̂⋆}_h) + (V̂^{π⋆}_h − V̂^{π̂⋆}_h) + (V⋆_h − V̂^{π⋆}_h)
  ≤ (V̂^{π̂⋆}_h − V^{π̂⋆}_h) + (V^{π⋆}_h − V̂^{π⋆}_h)`. -/
theorem eq_65 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] {H : ℕ}
    (P Phat : Fin H → S → A → S → ℝ) (r : Fin H → S → A → ℝ) (hM : IsFHMDP P r)
    (hPhat : ∀ h, IsTransitionKernel (Phat h))
    (sel : Fin H → S → (A → ℝ) → A) (hsel : IsArgmaxRule sel)
    (πstar : Fin H → S → A) (hstar : IsOptimal P r πstar) :
    ∀ (h : Fin H) (s : S),
      optValue P r h.val s - value P r (dpPolicy Phat r sel) h.val s =
          (value Phat r (dpPolicy Phat r sel) h.val s - value P r (dpPolicy Phat r sel) h.val s) +
            (value Phat r πstar h.val s - value Phat r (dpPolicy Phat r sel) h.val s) +
            (optValue P r h.val s - value Phat r πstar h.val s) ∧
      optValue P r h.val s - value P r (dpPolicy Phat r sel) h.val s ≤
          (value Phat r (dpPolicy Phat r sel) h.val s - value P r (dpPolicy Phat r sel) h.val s) +
            (value P r πstar h.val s - value Phat r πstar h.val s) := by sorry

end BreakingSample.FiniteHorizon
