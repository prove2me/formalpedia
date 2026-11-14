-- Prove2me | Theorems.Thm_ConsistentSubmodular_certificateReduction
-- name    : ConsistentSubmodular.certificateReduction
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:43.624062+00:00
-- url     : https://prove2.me/theorems/d2c14546-addb-475c-8801-955b9ff97f06
-- title:
--   Theorem 5 — certificates with linearly many segments give a deterministic $O(\varepsilon^{-3}\log(1/\varepsilon))$-consistent algorithm
-- statement:
--   For every $C\in\mathbb N$ there is a constant $K$ such that for every $\varepsilon\in(0,1)$ there is an integer $R\le K\varepsilon^{-3}\log(1/\varepsilon)$ with the following property. For every $\alpha\in(0,3/4]$: if every window instance $W$ with stages $0,\dots,m$ and one future element per stage (i.e. $R_{j+1}=R_j\cup\{v_{j+1}\}$ with $v_{j+1}\notin R_j$) admits an $(\alpha,\,C(m+1))$-certificate, then for every $n$, $k$ and nonnegative monotone submodular $f$ on $[n]$ there is a deterministic trajectory $(S_t)_{0\le t\le n}$ with $S_0=\emptyset$, $S_t\subseteq X_t$, $|S_t|\le k$, $|S_t\triangle S_{t-1}|\le R$, and
--   $$(\alpha-\varepsilon)\,f(A)\ \le\ f(S_t)\quad\text{for every } t \text{ and every } A\subseteq X_t,\ |A|\le k.$$
--   A $(\alpha,L)$-certificate consists of an anchor $p$ in the simplex that is persistent at every stage ($\alpha P_j\le H_j(p)$), an entry polygonal path in the simplex from $\delta_0$ to $p$ that is safe at stage $0$, an exit path from $p$ to $\delta_m$ that is safe at stage $m$, with at most $L$ segments in total.
--
--   Role: Appendices B.2.3 and B.2.4; the reduction from consistency to certificates. The recourse $R$ depends on $\varepsilon$ and $C$ only, and is fixed before $\alpha$, $n$, $k$, $f$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/MainResults.lean#L100-L104 (`ConsistentSubmodular.certificateReduction`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open ConsistentSubmodular

theorem ConsistentSubmodular.certificateReduction : CertificateReductionGoal := by sorry
