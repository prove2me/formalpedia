-- Prove2me | Theorems.Thm_ConsistentSubmodular_mixtureComparisons
-- name    : ConsistentSubmodular.mixtureComparisons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:38.560784+00:00
-- url     : https://prove2.me/theorems/61b8babb-9d8c-4fb4-885e-55e59ba3a136
-- title:
--   Lemma B.2 — mixture comparisons
-- statement:
--   Let $W$ be a window instance with stages $0,\dots,m$ and candidates $O_0,\dots,O_m\subseteq V_{\rm now}$, and let $Q$ be any buffer set. Write $H_Q(p)=\mathbb E\,f(Q\cup\bigcup_{i\in I(p)}O_i)$, where $I(p)$ contains each index $i$ independently with probability $p_i$, and $F_Q(z)=\mathbb E\,f(Q\cup S(z))$ for the random set $S(z)\subseteq V_{\rm now}$ containing each element $e$ independently with probability $z_e$. Let $z(p)=\sum_i p_i\mathbf 1_{O_i}$. Then:
--
--   1. for every $p\in[0,1]^{m+1}$ with $\sum_ip_i\le1$,
--   $$H_Q(p)\ \le\ F_Q\big(z(p)\big);$$
--   2. for every $p$ in the simplex $\Delta$ (i.e. $p_i\ge0$, $\sum_ip_i=1$),
--   $$H_Q(p)\ \le\ \sum_i p_i\, f(Q\cup O_i).$$
--
--   Role: Appendix B.2.1, inequalities (21) and (22); they compare the type-mixture value with the multilinear extension and with the linear mixture, and are used in the rounding of fractional windows.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/MainResults.lean#L133-L135 (`ConsistentSubmodular.mixtureComparisons`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open ConsistentSubmodular

theorem ConsistentSubmodular.mixtureComparisons : MixtureComparisonsGoal := by sorry
