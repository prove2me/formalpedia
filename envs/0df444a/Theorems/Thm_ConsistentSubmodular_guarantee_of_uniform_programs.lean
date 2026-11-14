-- Prove2me | Theorems.Thm_ConsistentSubmodular_guarantee_of_uniform_programs
-- name    : ConsistentSubmodular.guarantee_of_uniform_programs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:24.889203+00:00
-- url     : https://prove2.me/theorems/4f7540ab-39b1-4e5c-9841-4e009980812c
-- title:
--   Uniform transfer from rounded local programs to a consistent guarantee
-- statement:
--   Let $\alpha,\varepsilon\in\mathbb R$ and $N,H,R\in\mathbb N$ with $N\ge200$, $\alpha\le3/4$ and $20/N<\varepsilon$. Suppose the uniform program property holds: for all $n,k$, all objectives $f$ on $[n]$ and all transfer parameters $p$ for $(N,H,k)$, protected programs at level $\alpha-2/N$ with clock `transferClock f p`, rate $R$ and cardinality bound $p.\mathrm{core}+p.\mathrm{block}+H$ exist (`HasUniformPrograms α N H R`). Then
--   $$\texttt{ConsistentGuarantee}\ \alpha\ \varepsilon\ \big(2N(H+2(4N+1)+2)+R+2\big),$$
--   that is: for every $n$, every $k$ and every objective $f$ there is a trajectory $S_0=\emptyset,\dots,S_n$ with $S_t\subseteq X_t$, $|S_t|\le k$, $|S_{t+1}\triangle S_t|\le 2\,\mathrm{thr}+R+2$ (where $\mathrm{thr}=N(H+2(4N+1)+2)$ is the transfer threshold), and $(\alpha-\varepsilon)f(A)\le f(S_t)$ for every $t$ and every $A\subseteq X_t$ with $|A|\le k$.
--
--   Small budgets $k<\mathrm{thr}$ are handled by exact optimization, and a level at most $\varepsilon$ needs no programs since the empty trajectory already meets it.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/UniformTransfer.lean#L34-L63 (`ConsistentSubmodular.guarantee_of_uniform_programs`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_UniformTransfer

open ConsistentSubmodular

theorem ConsistentSubmodular.guarantee_of_uniform_programs {α ε : ℝ} {N H R : ℕ} (hN : 200 ≤ N)
    (hα : α ≤ 3 / 4) (hNε : 20 * ((1 : ℝ) / N) < ε)
    (hprograms : HasUniformPrograms α N H R) :
    ConsistentGuarantee α ε (2 * transferThreshold N H + R + 2) := by sorry
