-- Prove2me | Theorems.Thm_ConsistentSubmodular_accuracy_slack
-- name    : ConsistentSubmodular.accuracy_slack
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:40.028989+00:00
-- url     : https://prove2.me/theorems/f7f7252c-e339-4a30-8253-aeed8aa1b55e
-- title:
--   The accuracy parameter satisfies $20/N<\varepsilon$
-- statement:
--   For every real $\varepsilon>0$, the accuracy parameter $N=\texttt{accuracy}(\varepsilon)=\lfloor 20/\varepsilon\rfloor+200$ satisfies
--   $$\frac{20}{N}<\varepsilon .$$
--
--   This is the arithmetic fact guaranteeing that the loss $20/N$ incurred by the reduction is strictly below the target slack $\varepsilon$ and is used with $N\ge200$ to pick the integer accuracy of the reduction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/RecourseBound.lean#L33-L44 (`ConsistentSubmodular.accuracy_slack`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RecourseBound

open ConsistentSubmodular

theorem ConsistentSubmodular.accuracy_slack {ε : ℝ} (hε : 0 < ε) : 20 * ((1 : ℝ) / accuracy ε) < ε := by sorry
