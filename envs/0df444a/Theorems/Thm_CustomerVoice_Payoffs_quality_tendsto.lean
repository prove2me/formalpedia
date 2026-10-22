-- Prove2me | Theorems.Thm_CustomerVoice_Payoffs_quality_tendsto
-- name    : CustomerVoice.Payoffs.quality_tendsto
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:08:02.487772+00:00
-- url     : https://prove2.me/theorems/5f878d41-896e-4cee-b5e0-31a03c1cd725
-- title:
--   §3.4, p. 23 — the quality difference vanishes as selling cost tends to zero
-- statement:
--   Fix $\theta_H>\theta_L>0$, $0<\alpha,\gamma<1$, and $k>0$. For either buyer type $i$, vary only the positive selling-cost coefficient $s$. Then
--   $$\lim_{s\downarrow0}(q^O_i(s)-q^A_i(s))=0.$$
--
--   This convergence supplies the small-selling-cost comparison of the two designs. Each quality uses the same primitives at the current value of $s$.
--
--   **Formalization Note** The limit is one-sided over $s>0$. The reference model has $s>0$ in its standing assumptions; `withS` changes only that coefficient.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 23, §3.4, paragraph following Proposition 8

import Mathlib
import Definitions.Def_CustomerVoice_Payoffs_Setting

namespace CustomerVoice.Payoffs

theorem quality_tendsto (M : Model) (hM : M.Standing) :
    ∀ t : CustomerVoice.ALearn.BType,
      Filter.Tendsto (fun s' : ℝ => (M.withS s').qO t - (M.withS s').qA t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by sorry

end CustomerVoice.Payoffs
