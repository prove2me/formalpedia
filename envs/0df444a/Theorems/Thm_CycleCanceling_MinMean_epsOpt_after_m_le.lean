-- Prove2me | Theorems.Thm_CycleCanceling_MinMean_epsOpt_after_m_le
-- name    : CycleCanceling.MinMean.epsOpt_after_m_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:14:21.405975+00:00
-- url     : https://prove2.me/theorems/401da2db-0fc8-4859-a316-fcc11af51133
-- title:
--   Lemma 3.6 — $m$ minimum-mean cancellations reduce $\varepsilon(f)$ by a factor $1-1/n$
-- statement:
--   Let $G=(V,E)$ be a circulation network with $n=|V|$ vertices and $m=|E|$ arcs, and let $f_0,f_1,\dots,f_m$ be a run of $m$ iterations of the minimum-mean cycle-canceling algorithm. Then
--   $$
--   \varepsilon(f_m)\le\Bigl(1-\frac1n\Bigr)\varepsilon(f_0).
--   $$
--   Iterating this bound gives the geometric decrease of $\varepsilon(f)$ on which both iteration bounds of the paper (Theorems 3.7 and 3.9) rest.
--
--   **Formalization Note** $m$ is the number of arcs of $E$, counting $(v,w)$ and $(w,v)$ separately, as in the paper. A run starting from $f_0$ covers any $m$ consecutive iterations of the algorithm, since only the first circulation of a run is constrained.
-- source:
--   Goldberg, Tarjan, Finding Minimum-Cost Circulations by Canceling Negative Cycles, J. ACM 36(4), 1989, p. 878, Lemma 3.6 (proof ends p. 879)

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_Network
import Definitions.Def_CycleCanceling_MinMean_EpsOptimal
import Definitions.Def_CycleCanceling_MinMean_Algorithm

namespace CycleCanceling.MinMean

/-- Lemma 3.6 (p. 878): a sequence of `m = |E|` minimum-mean cycle cancellations reduces
`ε(f)` to at most `(1 - 1/n) ε(f)`, where `n = |V|`. -/
theorem epsOpt_after_m_le {V : Type*} [Fintype V] [DecidableEq V]
    (N : CircNetwork V) (F : ℕ → V → V → ℝ) (hrun : IsMinMeanRun N F N.E.card) :
    epsOpt N (F N.E.card) ≤ (1 - 1 / (Fintype.card V : ℝ)) * epsOpt N (F 0) := by sorry

end CycleCanceling.MinMean
