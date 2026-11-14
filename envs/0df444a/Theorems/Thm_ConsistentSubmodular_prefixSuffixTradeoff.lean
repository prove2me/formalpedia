-- Prove2me | Theorems.Thm_ConsistentSubmodular_prefixSuffixTradeoff
-- name    : ConsistentSubmodular.prefixSuffixTradeoff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:28.30635+00:00
-- url     : https://prove2.me/theorems/e17e3c04-b8c3-47cd-b6a8-cb7462bc40e4
-- title:
--   Theorem B.4 — the prefix–suffix tradeoff
-- statement:
--   Let $1/2<\beta\le3/4$, and let $W$ be a window instance with stages $0,\dots,m$. Put $\lambda_j=f(R_j)$, $g_j=P_j-\lambda_j$, $r_j=f(R_j\cup O_0)-\lambda_j$, $K_j=2g_j-r_j$, and
--   $$D=\max_j\big(2K_j-4(1-\beta)P_j\big).$$
--   Then:
--
--   1. there is an index $j$ with $K_j\ge D$;
--   2. for every index $c$ such that $K_c\ge D$ and $K_j<D$ for all $j>c$ (the last such index), with $A=O_0$, $B=O_c$ and the half mixture $H_{R_j}(A,B;1/2)$:
--      - (a) $H_{R_j}(A,B;1/2)\ge\beta P_j$ for all $j\le c$;
--      - (b) $H_{R_j}(A,B;1/2)\ge P_j/(2\beta)$ for all $j>c$;
--      - (c) there is a certificate at level $\alpha(\beta)=\min\{\beta,1/(2\beta)\}$ with at most $3$ segments, whose anchor is the point $\tfrac12\delta_0+\tfrac12\delta_c$ of the simplex, whose entry path has exactly one segment and whose exit path has at most two segments.
--
--   Role: Appendix B.2.2, equations (27) and (28); it proves Theorem 6 at $\beta=1/\sqrt2$ (where $\alpha(\beta)=1/\sqrt2$).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/MainResults.lean#L141-L144 (`ConsistentSubmodular.prefixSuffixTradeoff`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open ConsistentSubmodular

theorem ConsistentSubmodular.prefixSuffixTradeoff : PrefixSuffixTradeoffGoal := by sorry
