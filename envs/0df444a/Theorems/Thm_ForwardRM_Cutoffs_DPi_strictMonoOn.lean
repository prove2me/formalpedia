-- Prove2me | Theorems.Thm_ForwardRM_Cutoffs_DPi_strictMonoOn
-- name    : ForwardRM.Cutoffs.DPi_strictMonoOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:59:28.623355+00:00
-- url     : https://prove2.me/theorems/8f17f278-eea0-40be-9b30-43041ec4c37e
-- title:
--   §4.2, proof of Theorem 2 — DΠ^k_t(y¹) is strictly increasing in y¹
-- statement:
--   Suppose demand $N_t$ is weakly decreasing in the usual stochastic order. Let $1\le t\le T-1$ and $k\ge 1$. Then the difference $D\Pi^k_t(y^1)$ between selling one unit to $y^1$ today and waiting to sell at least one unit tomorrow is strictly increasing in $y^1$ on $[\underline v,\bar v]$:
--
--   $$
--   \underline v\le y^1<\hat y^1\le\bar v\ \Longrightarrow\ D\Pi^k_t(y^1)<D\Pi^k_t(\hat y^1).
--   $$
--
--   Raising $y^1$ raises the profit from selling today by the full increase of $m(y^1)$ and the profit from waiting by at most $\delta$ times that. This is the property that makes the root of $D\Pi^k_t$ unique in Theorem 2.
--
--   **Formalization Note** The demand hypothesis is the standing assumption of §4.2, where the claim is made.
-- source:
--   Board, Skrzypacz, Revenue Management with Forward-Looking Buyers, J. Political Economy 124(4) (2016), accepted manuscript of Feb. 6, 2015, p. 18, §4.2, proof of Theorem 2, paragraph after the display ("the second inequality follows from the envelope theorem")

import Mathlib
import Definitions.Def_ForwardRM_Cutoffs_Model
import Definitions.Def_ForwardRM_Cutoffs_ValueFunction
import Definitions.Def_ForwardRM_Cutoffs_Cutoff

namespace ForwardRM.Cutoffs

/-- Board–Skrzypacz, §4.2, proof of Theorem 2, p. 18: under weakly decreasing demand, in every
period `t ≤ T − 1` the function `DΠ^k_t(y¹)` is strictly increasing in `y¹` on `[v̲, v̄]`. -/
theorem DPi_strictMonoOn (M : Model) (hD : M.DecreasingDemand) (t k : ℕ) (ht : 1 ≤ t)
    (htT : t + 1 ≤ M.T) (hk : 1 ≤ k) :
    StrictMonoOn (M.DPi t k) (Set.Icc M.vlo M.vhi) := by sorry

end ForwardRM.Cutoffs
