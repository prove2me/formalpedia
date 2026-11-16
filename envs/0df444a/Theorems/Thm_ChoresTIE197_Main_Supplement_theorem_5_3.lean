-- Prove2me | Theorems.Thm_ChoresTIE197_Main_Supplement_theorem_5_3
-- name    : ChoresTIE197.Main.Supplement.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:01:17.04448+00:00
-- url     : https://prove2.me/theorems/da6b170b-1718-46c9-ac41-da98a58f526f
-- title:
--   Theorem 5.3 — impossibility below 13/12 for every n≥4
-- statement:
--   For every integer $n\ge4$ and every real $\alpha<13/12$, there is a finite number $m$ of chores such that every complete payment-free randomized mechanism $F$ on $n$ agents and $m$ chores satisfies
--   $$
--   \operatorname{TIE}_{+}(F)\ \Longrightarrow\ \neg\operatorname{MMS}_{+}(\alpha,F).
--   $$
--   Both predicates concern the same mechanism on all nonnegative additive report profiles with positive total in every row. The conclusion provides an ex-post obstruction: some positive profile, supported complete allocation and agent violate the claimed ratio. It imposes no lower cutoff on $\alpha$ and makes no claim at $\alpha=13/12$. The chore count is chosen before the mechanism, rather than requiring impossibility for every $m$.
--
--   This companion theorem supplies a uniform lower bound independent of the positive goal, and excludes the same guarantee for mechanisms on the full nonnegative domain. No symmetry, equal marginals, ex-ante envy-freeness or runtime restriction is assumed.
--
--   Differences from the source:
--   - encoding: finite agents and chores, arbitrary nonnegative additive costs, complete payment-free randomized allocations → Fin-indexed nonnegative real singleton tables and the published PMF on complete owner maps, with cost MMS the sign dual of utility MMS; reason: finite relabeling and sign duality preserve every source instance, empty bundles, real probabilities and support-wise guarantees
--   - encoding: the standing convention on p.7 assumes positive MMS for every agent → TIEOn Positive F and MMSOn Positive α F on all profiles with positive row total; reason: for nonnegative additive costs and n≥2, positive total is equivalent to positive MMS; no singleton positivity is required, and full-domain guarantees restrict to this domain
--   - encoding: no mechanism guarantees the stated ratio on every finite additive chore instance → for each fixed n and real α below the threshold there exists m such that every F on n agents and m chores is obstructed; reason: the finite hard constructions choose a chore count before the candidate mechanism; negating the uniform ex-post guarantee yields some positive profile, supported allocation and violating agent
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), Theorem 5.3, printed p.28, PDF p.28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Setting

namespace ChoresTIE197.Main.Supplement

/-- Theorem 5.3, printed/PDF pp.28–29. Arbitrary complete payment-free
randomized mechanisms, with no EF, equal-marginal, symmetry or runtime premise. -/
theorem theorem_5_3 (n : ℕ) (hn : 4 ≤ n) (α : ℝ) (hα : α < 13 / 12) :
    ∃ m : ℕ, ∀ F : Mechanism n m,
      TIEOn Positive F → ¬ MMSOn Positive α F := by sorry

end ChoresTIE197.Main.Supplement
