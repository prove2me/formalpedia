-- Prove2me | Theorems.Thm_CrowdfundRM_Identical_proposition_6_i
-- name    : CrowdfundRM.Identical.proposition_6_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:08:11.921657+00:00
-- url     : https://prove2.me/theorems/03f06c36-6c79-4007-a0d8-d4c723432236
-- title:
--   Proposition 6(i), p. 19 — identical valuations with v_i ≤ v_h: an optimal campaign exists, and every optimum has p* ≥ v_i/e and T* ≤ 1/r
-- statement:
--   Consider the crowdfunding model with standing assumptions, where every independent backer values the project at $v_i$ and every herding backer at $v_h$, with $0<v_i\le\bar v$ and $0<v_h\le\bar v$. The creator chooses a pledge level $p$ and a duration $T$ to maximize the revenue $\pi(p,T)=p\,n(p,T)$ over the set
--
--   $$0<p\le\bar v,\qquad 0\le T\le\frac1r\ln\frac{\bar v}{p},\qquad T\le\frac1r\ln\frac{v_i}{p},$$
--
--   the last constraint ensuring that independent backers pledge from the start of the campaign. If $v_i\le v_h$, then a maximizer $(p^*,T^*)$ exists, and every maximizer satisfies
--
--   $$p^*\ge\frac{v_i}{e}\qquad\text{and}\qquad T^*\le\frac1r.$$
--
--   When herding backers value the project at least as much as independent ones, the optimal campaign therefore uses a pledge level that is not too low and a duration that is short relative to the discount horizon $1/r$.
--
--   **Formalization Note.** The paper presupposes an optimum; existence is stated explicitly so that the bounds are not vacuous. The maximizer is not claimed to be unique, so the bounds are stated for every maximizer. The added hypotheses are the standing assumptions and $p>0$ in the feasible set.
-- source:
--   Zhang, Savin, Veeraraghavan, Revenue Management in Crowdfunding, SSRN 3065267 (manuscript of May 26, 2021), p. 19, Proposition 6(i)

import Mathlib
import Definitions.Def_CrowdfundRM_Identical_Setting

namespace CrowdfundRM.Identical

theorem proposition_6_i (M : Campaign) (hM : M.Standing) (vi vh : ℝ) (hv : IdenticalVals M vi vh)
    (hle : vi ≤ vh) :
    (∃ p T, IsMaxOn₂ (revenue M) (Feasible6 M vi) p T) ∧
      ∀ p T, IsMaxOn₂ (revenue M) (Feasible6 M vi) p T →
        vi / Real.exp 1 ≤ p ∧ T ≤ 1 / M.r := by sorry

end CrowdfundRM.Identical
