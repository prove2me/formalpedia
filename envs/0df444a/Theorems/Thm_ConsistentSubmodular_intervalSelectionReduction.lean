-- Prove2me | Theorems.Thm_ConsistentSubmodular_intervalSelectionReduction
-- name    : ConsistentSubmodular.intervalSelectionReduction
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:27.367207+00:00
-- url     : https://prove2.me/theorems/fd891f23-d129-489b-ab76-185c729a2fae
-- title:
--   Lemma 2 — adaptivity gap at least $\alpha$ gives $\alpha$-addition-robust distributions
-- statement:
--   Let $\alpha\in[0,1]$. Assume that every interval-selection instance $(\ell,r,p)$ (any $N\in\mathbb N$, intervals $[\ell_i,r_i]$ with $0\le\ell_i\le r_i$ indexed by $\{0,\dots,N\}$, and a probability vector $p$) has adaptivity gap
--   $$\Gamma(\ell,r,p)\ \ge\ \alpha .$$
--   Then for every $n$ and every window instance $W$ on the ground set $[n]$ (an objective $f$ that is nonnegative, monotone and submodular, present elements $V_{\rm now}$, budget $\kappa$, nested arrival prefixes $\emptyset=R_0\subseteq\dots\subseteq R_m$ disjoint from $V_{\rm now}$, and candidates $O_j\subseteq V_{\rm now}$, $|O_j|\le\kappa$, maximizing $f(O\cup R_j)$), there is an $\alpha$-addition-robust distribution $w$: a probability distribution on sets $S\subseteq V_{\rm now}$ with $|S|\le\kappa$ such that for every stage $j$
--   $$\mathbb E_{S\sim w}\,f(S\cup R_j)\ \ge\ \alpha\, f(O_j\cup R_j).$$
--   No restriction to one arrival per stage is imposed on $W$.
--
--   Role: this is the reduction from the clairvoyant addition-robust problem to interval selection (Appendix A.4); together with Lemmas 3 and 4 it yields addition-robust distributions at level $\xi_\star$ for every instance.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/MainResults.lean#L53-L56 (`ConsistentSubmodular.intervalSelectionReduction`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open ConsistentSubmodular

theorem ConsistentSubmodular.intervalSelectionReduction : IntervalSelectionReductionGoal := by sorry
