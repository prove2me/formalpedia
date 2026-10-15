-- Prove2me | Theorems.Thm_CrowdfundRM_Identical_corollary_1
-- name    : CrowdfundRM.Identical.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:08:11.219891+00:00
-- url     : https://prove2.me/theorems/f9faea07-b265-4fc6-9444-8a347d35e171
-- title:
--   Corollary 1, pp. 10–11 — with identical valuations, the pledge counts (5) and (11) equal the explicit formulas (14) and (15)
-- statement:
--   Consider the crowdfunding model with standing assumptions, and suppose every independent backer values the project at $v_i$ and every herding backer at $v_h$, where $0<v_i,v_h\le\bar v$. Let the pledge level $p$ and the duration $T$ satisfy
--
--   $$0<p\le\min\big(v_ie^{-rT},\,v_h\big).$$
--
--   Write $c^+=\big(T-\frac1r\ln(v_h/p)\big)^+$ for the time at which herding backers begin to pledge. Then for every $t\in[0,T]$ the closed-form pledge counts (5) and (11) satisfy
--
--   $$n^p_i(t,p,T)=\hat I\big(1-e^{-kt}\big),$$
--
--   $$n^p_h(t,p,T)=\hat I\,\mathbb I(t-c^+)\Big(\big(e^{\Lambda_h qp(t-c^+)}-1\big)-\frac{\Lambda_h qp}{\Lambda_h qp+k}\,e^{-kc^+}\Big(e^{\Lambda_h qp(t-c^+)}-e^{-k(t-c^+)}\Big)\Big),$$
--
--   where $\mathbb I(x)=1$ for $x\ge0$ and $0$ for $x<0$.
--
--   The condition on $p$ means that independent backers pledge from the start of the campaign and herding backers are not priced out. These explicit formulas are what make the optimization of the pledge level and the duration tractable when valuations are deterministic.
--
--   **Formalization Note.** The positive part is `max x 0` and is written out at each occurrence. $\frac1r\ln(v_h/p)$ is written `1 / r * log (vh / p)`. The hypothesis of identical valuations includes $0<v_i,v_h\le\bar v$, as in Propositions 3(b) and 6; under $0<p\le\min(v_ie^{-rT},v_h)$ it adds nothing beyond $v_i,v_h\le\bar v$, which the valuation support requires.
-- source:
--   Zhang, Savin, Veeraraghavan, Revenue Management in Crowdfunding, SSRN 3065267 (manuscript of May 26, 2021), pp. 10–11, Corollary 1, (14)–(16); (58)–(59) p. 29

import Mathlib
import Definitions.Def_CrowdfundRM_Identical_Setting

namespace CrowdfundRM.Identical

theorem corollary_1 (M : Campaign) (hM : M.Standing) (vi vh : ℝ) (hv : IdenticalVals M vi vh)
    (p T : ℝ) (hp : 0 < p) (hpm : p ≤ min (vi * Real.exp (-M.r * T)) vh) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      npi M p T t = M.Ihat * (1 - Real.exp (-M.k * t)) ∧
      nph M p T t =
        M.Ihat * ind (t - max (T - 1 / M.r * Real.log (vh / p)) 0) *
          ((Real.exp (M.Lh * M.q * p * (t - max (T - 1 / M.r * Real.log (vh / p)) 0)) - 1) -
            (M.Lh * M.q * p / (M.Lh * M.q * p + M.k)) *
              Real.exp (-M.k * max (T - 1 / M.r * Real.log (vh / p)) 0) *
              (Real.exp (M.Lh * M.q * p * (t - max (T - 1 / M.r * Real.log (vh / p)) 0)) -
                Real.exp (-M.k * (t - max (T - 1 / M.r * Real.log (vh / p)) 0)))) := by sorry

end CrowdfundRM.Identical
