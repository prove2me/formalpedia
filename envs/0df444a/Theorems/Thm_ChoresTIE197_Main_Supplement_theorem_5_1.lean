-- Prove2me | Theorems.Thm_ChoresTIE197_Main_Supplement_theorem_5_1
-- name    : ChoresTIE197.Main.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:59:40.685456+00:00
-- url     : https://prove2.me/theorems/b406a52b-1354-415a-a8d3-f9466f20b14f
-- title:
--   Theorem 5.1 — exact lower bounds for every number of agents
-- statement:
--   For every integer $n\ge2$ and every real $\alpha<\alpha_n$, with the exact parity-dependent threshold defined above, there is a finite number $m$ of chores such that every complete payment-free randomized mechanism $F$ on $n$ agents and $m$ chores satisfies
--   $$
--   \operatorname{TIE}_{+}(F)\ \Longrightarrow\ \neg\operatorname{MMS}_{+}(\alpha,F).
--   $$
--   Here the subscript $+$ denotes all nonnegative additive report profiles with positive total cost in each row, as in the source's positive-MMS convention. Truthfulness compares every agent's true and alternative reports remaining in this domain, with opponents fixed. The negated guarantee means there are a positive profile, an allocation of nonzero probability and an agent whose own bundle costs strictly more than $\alpha$ times her actual MMS. In particular, no mechanism on the full nonnegative domain can guarantee the ratio either. The chore count is chosen before $F$; it need not work for every chore count. All real $\alpha$ below the threshold are covered, including $\alpha<1$; equality with the threshold is not excluded.
--
--   This companion theorem is not used to prove the published positive goal. It combines the two-agent bound, the parity-sensitive construction of §5.2 and the uniform large-agent bound, without symmetry, envy-freeness, equal-marginal or computational assumptions.
--
--   Differences from the source:
--   - encoding: finite agents and chores, arbitrary nonnegative additive costs, complete payment-free randomized allocations → Fin-indexed nonnegative real singleton tables and the published PMF on complete owner maps, with cost MMS the sign dual of utility MMS; reason: finite relabeling and sign duality preserve every source instance, empty bundles, real probabilities and support-wise guarantees
--   - encoding: the standing convention on p.7 assumes positive MMS for every agent → TIEOn Positive F and MMSOn Positive α F on all profiles with positive row total; reason: for nonnegative additive costs and n≥2, positive total is equivalent to positive MMS; no singleton positivity is required, and full-domain guarantees restrict to this domain
--   - encoding: no mechanism guarantees the stated ratio on every finite additive chore instance → for each fixed n and real α below the threshold there exists m such that every F on n agents and m chores is obstructed; reason: the finite hard constructions choose a chore count before the candidate mechanism; negating the uniform ex-post guarantee yields some positive profile, supported allocation and violating agent
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), Theorem 5.1, printed p.24, PDF p.24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Setting
import Definitions.Def_ChoresTIE197_Main_Supplement_threshold

namespace ChoresTIE197.Main.Supplement

/-- Theorem 5.1, printed/PDF p.24, including every parity and n = 2.
The positive-row-total domain is the source's standing positive-MMS convention.
The hard number of chores is chosen before the candidate mechanism. -/
theorem theorem_5_1 (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα : α < threshold n) :
    ∃ m : ℕ, ∀ F : Mechanism n m,
      TIEOn Positive F → ¬ MMSOn Positive α F := by sorry

end ChoresTIE197.Main.Supplement
