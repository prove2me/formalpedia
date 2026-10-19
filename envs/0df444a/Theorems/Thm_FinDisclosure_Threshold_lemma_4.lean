-- Prove2me | Theorems.Thm_FinDisclosure_Threshold_lemma_4
-- name    : FinDisclosure.Threshold.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:27.35719+00:00
-- url     : https://prove2.me/theorems/ecbd15d0-c164-4b59-86aa-3c6dada83a57
-- title:
--   Lemma 4, p. 36 — Ŝ = [ŝ, 1]: the states with nonnegative marginal contribution form an upper interval
-- statement:
--   Assume the standing assumptions of the model, and let $\kappa \ge 0$, playing the role of the ratio $\alpha_3/q$ of the dual multiplier of the financing constraint to $q$. Let
--   $$\hat S = \Big\{ s \in [0,1] \;:\; \big(s - c(s) + B + \lambda(c(s) - I)\big) + \kappa\,\big(c(s) - I\big) \ge 0 \Big\},$$
--   the set of states whose marginal contribution to the dual objective in the proof of Lemma 4 (p. 37) is nonnegative. Then $\hat S$ is either empty or an interval
--   $$\hat S = [\hat s, 1] \quad\text{for some } \hat s \in [0,1].$$
--
--   This is why the optimal high posterior puts weight on all states above a cutoff, which is the threshold form of the optimal disclosure policy.
--
--   **Formalization Note** The set is defined by the inequality in the paper's proof of Lemma 4 ("$s \in \hat S$ if and only if …"), and the conclusion is the set identity, not monotonicity alone. The empty case is allowed because the inequality may fail everywhere; in the paper $\hat S$ is the support of $\mu_h$ and is nonempty. No hypothesis $\lambda I \le B$ is needed.
-- source:
--   Szydlowski, Optimal Financing and Disclosure, working paper (version of March 2017), p. 36 (PDF 36), Lemma 4; proof p. 37 (PDF 37)

import Mathlib
import Definitions.Def_FinDisclosure_Threshold_Model

open MeasureTheory ProbabilityTheory Set

namespace FinDisclosure.Threshold

/-- Lemma 4, p. 36 (proof p. 37): for a multiplier `κ = α3 / q ≥ 0`, the set `Ŝ` of states
`s ∈ [0,1]` with `s - c(s) + B + λ(c(s) - I) + κ (c(s) - I) ≥ 0` is an interval `[ŝ, 1]`
(or empty). -/
theorem lemma_4 (c f0 : ℝ → ℝ) (I B lam : ℝ) (hS : Standing c f0 I B lam)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    {s ∈ Icc (0:ℝ) 1 | 0 ≤ gE c I B lam s + κ * (c s - I)} = ∅ ∨
      ∃ shat ∈ Icc (0:ℝ) 1,
        {s ∈ Icc (0:ℝ) 1 | 0 ≤ gE c I B lam s + κ * (c s - I)} = Icc shat 1 := by sorry

end FinDisclosure.Threshold
