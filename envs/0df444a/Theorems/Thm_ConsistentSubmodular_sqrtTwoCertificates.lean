-- Prove2me | Theorems.Thm_ConsistentSubmodular_sqrtTwoCertificates
-- name    : ConsistentSubmodular.sqrtTwoCertificates
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:35.261314+00:00
-- url     : https://prove2.me/theorems/ac8d743b-107e-4a85-9d09-95dde7ecabff
-- title:
--   Theorem 6 — every window instance has a $(1/\sqrt2,3)$-certificate
-- statement:
--   For every $n$ and every window instance $W$ on $[n]$ with stages $0,\dots,m$ (any $m$, arrivals not necessarily one per stage), there exists a $(1/\sqrt2,\,3)$-certificate: an anchor $p$ in the simplex $\Delta$ on $\{0,\dots,m\}$ with $\tfrac1{\sqrt2}P_j\le H_j(p)$ for all stages $j$, an entry polygonal path in $\Delta$ from $\delta_0$ to $p$ along which $H_0\ge\tfrac1{\sqrt2}P_0$, an exit polygonal path in $\Delta$ from $p$ to $\delta_m$ along which $H_m\ge\tfrac1{\sqrt2}P_m$, and in total at most $3$ segments. Here $P_j=f(O_j\cup R_j)$ and $H_j(p)=\mathbb E\,f(R_j\cup\bigcup_{i\in I(p)}O_i)$ with $I(p)$ containing each $i$ independently with probability $p_i$.
--
--   Role: Appendix B.2.2; it is the case $\beta=1/\sqrt2$ of Theorem B.4 and gives a bounded number of segments independent of $m$ at level $1/\sqrt2$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/MainResults.lean#L106-L109 (`ConsistentSubmodular.sqrtTwoCertificates`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open ConsistentSubmodular

theorem ConsistentSubmodular.sqrtTwoCertificates : SqrtTwoCertificatesGoal := by sorry
