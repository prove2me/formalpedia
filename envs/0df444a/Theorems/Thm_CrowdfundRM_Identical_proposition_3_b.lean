-- Prove2me | Theorems.Thm_CrowdfundRM_Identical_proposition_3_b
-- name    : CrowdfundRM.Identical.proposition_3_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:08:00.601809+00:00
-- url     : https://prove2.me/theorems/96728325-072e-4f9e-9f1c-484c6d6b0b5e
-- title:
--   Proposition 3(b), p. 13 — identical valuations, Λ_h q v_h/r < 1, k/r > 2: for every sufficiently long fixed duration T the optimal pledge level is v_i e^{−rT}
-- statement:
--   Consider the crowdfunding model with standing assumptions, where every independent backer values the project at $v_i$ and every herding backer at $v_h$, with $0<v_i\le\bar v$ and $0<v_h\le\bar v$. Suppose there is $\delta$ with
--
--   $$\frac{\Lambda_h q v_h}{r}\le\delta<1\qquad\text{and}\qquad \frac kr>2.$$
--
--   Then there is $T_0>0$ such that for every fixed campaign duration $T\ge T_0$ the pledge level
--
--   $$p^*(T)=v_ie^{-rT}$$
--
--   is the unique maximizer of the revenue $p\mapsto\pi(p,T)$ over the pledge levels allowed by problem (18) at that duration, namely $0<p\le\bar v$ with $T\le\frac1r\ln(\bar v/p)$.
--
--   The optimal pledge level for a long fixed duration is thus the highest one at which every independent backer still pledges from the start of the campaign. This is the limited-flexibility counterpart of the jointly optimal campaign in Proposition 6.
--
--   **Formalization Note.** "Sufficiently long" is the existence of a threshold $T_0>0$, which the paper does not specify. "The optimal pledge level" is read as the unique maximizer. The range of $p$ is (18)'s, not the narrower one of Proposition 6. $\delta$ is kept as a free variable as printed. The added hypotheses are the standing assumptions $\hat I,k,r,\bar v>0$, $\Lambda_h,q\ge0$ and $p>0$ in the feasible set.
-- source:
--   Zhang, Savin, Veeraraghavan, Revenue Management in Crowdfunding, SSRN 3065267 (manuscript of May 26, 2021), p. 13, Proposition 3(b)

import Mathlib
import Definitions.Def_CrowdfundRM_Identical_Setting

namespace CrowdfundRM.Identical

theorem proposition_3_b (M : Campaign) (hM : M.Standing) (vi vh : ℝ) (hv : IdenticalVals M vi vh)
    (δ : ℝ) (hδ : M.Lh * M.q * vh / M.r ≤ δ) (hδ1 : δ < 1) (hkr : 2 < M.k / M.r) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      CrowdfundRM.Triangular.IsUniqueMaxOn (fun p => revenue M p T) {p | M.Feasible p T}
        (vi * Real.exp (-M.r * T)) := by sorry

end CrowdfundRM.Identical
