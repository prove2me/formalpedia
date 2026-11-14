-- Prove2me | Theorems.Thm_ConsistentSubmodular_consecutiveIntervalReduction
-- name    : ConsistentSubmodular.consecutiveIntervalReduction
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:15.890136+00:00
-- url     : https://prove2.me/theorems/288fa153-248d-4872-aed3-6fcae8d7fc95
-- title:
--   Lemma 3 — reduction to nonincreasing consecutive intervals
-- statement:
--   Let $\alpha\in[0,1]$. Suppose that $\Gamma(\ell,r,p)\ge\alpha$ holds for every interval-selection instance (for every $N$) that has nonincreasing consecutive intervals, i.e. $\ell_0=0$, $\ell_{i+1}=r_i$ for $i<N$, $r_0-\ell_0\ge\dots\ge r_N-\ell_N>0$, and whose distribution $p$ is equalizing, i.e. all fixed intervals have the same expected value $\mathbb E_{j\sim p}[v(i,j)]$, where $v(i,j)=\ell_j+|[\ell_i,r_i]\cap[\ell_j,\infty)|$. Then
--   $$\Gamma(\ell,r,p)\ \ge\ \alpha$$
--   for every interval-selection instance $(\ell,r,p)$ without further restriction. Here $\Gamma$ is the ratio $\max_i\mathbb E_{j\sim p}v(i,j)\,/\,\mathbb E_{j\sim p}\max_i v(i,j)$, taken to be $1$ if the denominator is $0$.
--
--   Role: Appendix A.5; it reduces the adaptivity-gap bound for general interval selection to the structured family treated in Lemma 4.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/MainResults.lean#L58-L61 (`ConsistentSubmodular.consecutiveIntervalReduction`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open ConsistentSubmodular

theorem ConsistentSubmodular.consecutiveIntervalReduction : ConsecutiveIntervalReductionGoal := by sorry
