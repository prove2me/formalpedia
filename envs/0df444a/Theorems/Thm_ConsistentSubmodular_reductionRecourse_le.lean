-- Prove2me | Theorems.Thm_ConsistentSubmodular_reductionRecourse_le
-- name    : ConsistentSubmodular.reductionRecourse_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:47.502194+00:00
-- url     : https://prove2.me/theorems/04ad6626-1ad8-4b6d-ad40-f462ab7094b5
-- title:
--   Recourse constant is $O(N^3\log N)$
-- statement:
--   For every $C\in\mathbb N$ and $N\ge1$, with $S=(C+1)(3N+2)$,
--   $$\texttt{reductionRecourse}\ N\ S\ \le\ N^3\big(A_C+800\ln N\big),$$
--   where $A_C=\texttt{rateConstant}\,C=256\ln\big(1200(C+1)\big)+1034+31220(C+1)$ and
--   $$\texttt{reductionRecourse}\ N\ S=2\,\mathrm{thr}\big(N,H\big)+4N(4N+1)(3L+1)+2,$$
--   with $\mathrm{thr}(N,H)=N(H+2(4N+1)+2)$, $H=\texttt{familyHeavy}\ N\ S$ and $L=\texttt{familyLength}\ S$.
--
--   The recourse constant of the reduction is thus $O(N^3\log N)$ with an explicit constant depending only on $C$, uniformly for the segment budget $S=(C+1)(3N+2)$ coming from $C$-consistent certificates.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/RecourseBound.lean#L126-L153 (`ConsistentSubmodular.reductionRecourse_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RecourseBound

open ConsistentSubmodular

theorem ConsistentSubmodular.reductionRecourse_le (C N : ℕ) (hN : 1 ≤ N) :
    (reductionRecourse N ((C + 1) * (3 * N + 2)) : ℝ) ≤
      (N : ℝ) ^ 3 * (rateConstant C + 800 * Real.log N) := by sorry
