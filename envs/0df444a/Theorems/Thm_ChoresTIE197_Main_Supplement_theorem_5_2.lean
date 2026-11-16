-- Prove2me | Theorems.Thm_ChoresTIE197_Main_Supplement_theorem_5_2
-- name    : ChoresTIE197.Main.Supplement.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:00:20.577653+00:00
-- url     : https://prove2.me/theorems/87c6ac25-cc41-419e-8b91-68a6aa5a053f
-- title:
--   Theorem 5.2 — two-agent impossibility below 4/3
-- statement:
--   For every real $\alpha<4/3$, there is a finite number $m$ of chores such that for every complete payment-free randomized two-agent mechanism $F$,
--   $$
--   \operatorname{TIE}_{+}(F)\ \Longrightarrow\ \neg\operatorname{MMS}_{+}(\alpha,F).
--   $$
--   The domain consists of arbitrary nonnegative additive reports with positive total cost for each agent. TIE ranges over every unilateral deviation within that domain; failure of ex-post MMS means some positive profile, some supported complete allocation and some agent violate the ratio. The same $F$ is compared at all profiles. The count $m$ is existential, chosen before $F$, and no lower bound on $\alpha$ is imposed.
--
--   This companion theorem establishes the two-agent lower bound separately from the positive goal. In particular, it excludes a better-than-$4/3$ guarantee on the full nonnegative domain, without requiring equal marginals, symmetry, ex-ante envy-freeness or efficient computation.
--
--   Differences from the source:
--   - encoding: finite agents and chores, arbitrary nonnegative additive costs, complete payment-free randomized allocations → Fin-indexed nonnegative real singleton tables and the published PMF on complete owner maps, with cost MMS the sign dual of utility MMS; reason: finite relabeling and sign duality preserve every source instance, empty bundles, real probabilities and support-wise guarantees
--   - encoding: the standing convention on p.7 assumes positive MMS for every agent → TIEOn Positive F and MMSOn Positive α F on all profiles with positive row total; reason: for nonnegative additive costs and n≥2, positive total is equivalent to positive MMS; no singleton positivity is required, and full-domain guarantees restrict to this domain
--   - encoding: no mechanism guarantees the stated ratio on every finite additive chore instance → for each fixed n and real α below the threshold there exists m such that every F on n agents and m chores is obstructed; reason: the finite hard constructions choose a chore count before the candidate mechanism; negating the uniform ex-post guarantee yields some positive profile, supported allocation and violating agent
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), Theorem 5.2, printed p.24, PDF p.24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Setting

namespace ChoresTIE197.Main.Supplement

/-- Theorem 5.2, printed/PDF pp.24–26. There is no lower cutoff on α;
for α < 1 a one-chore positive instance already obstructs the guarantee. -/
theorem theorem_5_2 (α : ℝ) (hα : α < 4 / 3) :
    ∃ m : ℕ, ∀ F : Mechanism 2 m,
      TIEOn Positive F → ¬ MMSOn Positive α F := by sorry

end ChoresTIE197.Main.Supplement
