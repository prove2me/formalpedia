-- Prove2me | Theorems.Thm_CycleCanceling_MinMean_isEpsFixed_of_reducedCost
-- name    : CycleCanceling.MinMean.isEpsFixed_of_reducedCost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:14:54.766634+00:00
-- url     : https://prove2.me/theorems/932da085-7f39-4881-b10e-29cf0307a0cc
-- title:
--   Theorem 3.8 — an arc with $|c_p(v,w)| \ge 2n\varepsilon$ is $\varepsilon$-fixed
-- statement:
--   Let $\varepsilon>0$, let $n=|V|$, and let $f$ be a circulation that is $\varepsilon$-optimal with respect to a price function $p$. If an arc $(v,w)\in E$ satisfies
--   $$
--   |c_p(v,w)|\ge 2n\varepsilon ,
--   $$
--   then $(v,w)$ is $\varepsilon$-fixed: every two $\varepsilon$-optimal circulations have the same flow on $(v,w)$.
--
--   This generalizes a theorem of Tardos and is the source of strong polynomiality: once $\varepsilon(f)$ has dropped far enough, an arc of the canceled cycle is frozen for the rest of the run.
-- source:
--   Goldberg, Tarjan, Finding Minimum-Cost Circulations by Canceling Negative Cycles, J. ACM 36(4), 1989, p. 879, Theorem 3.8

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_Network
import Definitions.Def_CycleCanceling_MinMean_EpsOptimal

namespace CycleCanceling.MinMean

/-- Theorem 3.8 (p. 879): let `ε > 0`, let the circulation `f` be `ε`-optimal with respect to
a price function `p`, and let `(v, w)` be an arc with `|c_p(v, w)| ≥ 2nε`, `n = |V|`. Then
`(v, w)` is `ε`-fixed. -/
theorem isEpsFixed_of_reducedCost {V : Type*} [Fintype V] [DecidableEq V]
    (N : CircNetwork V) (ε : ℝ) (hε : 0 < ε) (f : V → V → ℝ) (hf : IsCirculation N f)
    (p : V → ℝ) (hfp : IsEpsOptimalWrt N f ε p) (v w : V) (hvw : (v, w) ∈ N.E)
    (hbig : 2 * (Fintype.card V : ℝ) * ε ≤ |reducedCost N p v w|) :
    IsEpsFixed N ε v w := by sorry

end CycleCanceling.MinMean
