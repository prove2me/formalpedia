-- Prove2me | Theorems.Thm_ConsistentSubmodular_reductionRecourse_rate
-- name    : ConsistentSubmodular.reductionRecourse_rate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:06.39321+00:00
-- url     : https://prove2.me/theorems/1b0c9199-0a11-49db-bb90-7b389c877dc9
-- title:
--   Recourse constant is at most $K_C\,\varepsilon^{-3}\log(1/\varepsilon)$
-- statement:
--   For every $C\in\mathbb N$ and every real $\varepsilon$ with $0<\varepsilon<3/4$, writing $N=\texttt{accuracy}(\varepsilon)=\lfloor20/\varepsilon\rfloor+200$,
--   $$\texttt{reductionRecourse}\ N\ \big((C+1)(3N+2)\big)\ \le\ K_C\Big(\frac1\varepsilon\Big)^{3}\ln\frac1\varepsilon,$$
--   where $K_C=\texttt{reductionConstant}\,C=220^3\,(4A_C+20000)$ and $A_C=256\ln(1200(C+1))+1034+31220(C+1)$.
--
--   This converts the bound $O(N^3\log N)$ on the recourse of the reduction into a bound in terms of the slack $\varepsilon$, using $N\le 220/\varepsilon$; it gives the constant $K_C$ of Theorem 5.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/RecourseBound.lean#L184-L211 (`ConsistentSubmodular.reductionRecourse_rate`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RecourseBound

open ConsistentSubmodular

theorem ConsistentSubmodular.reductionRecourse_rate (C : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 3 / 4) :
    (reductionRecourse (accuracy ε) ((C + 1) * (3 * accuracy ε + 2)) : ℝ) ≤
      reductionConstant C * (1 / ε) ^ 3 * Real.log (1 / ε) := by sorry
