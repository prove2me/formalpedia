-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_algLS_spec
-- name    : BCFGJPSSV26.Greedy.algLS_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:40:50.792919+00:00
-- url     : https://prove2.me/theorems/e4f31301-1c1a-4efd-83dc-4fa5aab14743
-- title:
--   Guarantee of the large-$\varepsilon$ algorithm: at most $k$ facilities of cost at most $4\,\mathrm{opt}_k$
-- statement:
--   This is the guarantee of the algorithm used for $\varepsilon\ge4$ in Theorem 1.2 of Part I: a local search that opens at most $k$ facilities, of cost at most $4\,\mathrm{opt}_k$.
--
--   **Setting.** Let $I$ be a $k$-median instance: $n$ clients and $m\ge1$ facilities in a pseudometric space with rational distances, and $k\ge1$. Write $\mathrm{cost}(S)=\sum_j\min_{i\in S}d(j,i)$, and $\mathrm{opt}_k$ for the least cost of a nonempty set of at most $k$ facilities.
--
--   **The algorithm.** The trivial solution consists of the nearest facility of every client (least index on ties), without repetitions. If $n=0$ the output is the facility $0$. If the trivial solution has at most $k$ facilities, it is the output. Otherwise the output is that of the local search of Part II with $N=201$: start from the facilities $0,\dots,k-1$; a swap is a list of $p=24N=4824$ numbers $x<km$, each of which puts facility $x\bmod m$ at position $\lfloor x/m\rfloor$ unless it is already open; a step applies the first swap, in a fixed enumeration cut at $B$, that lowers the exact cost below $(1-\tfrac1{Nk})$ times the current cost; at most $B=(|I|+2)^{2p+2}$ steps are made, where $|I|$ is the length of the encoding of $I$.
--
--   **Statement.** The output $S$ satisfies:
--
--   1. $S$ is a nonempty list of distinct facilities of $I$;
--   2. $|S|\le k$;
--   3. the cost bound
--   $$\mathrm{cost}(S)\ \le\ 4\cdot\mathrm{opt}_k .$$
--
--   For $\varepsilon\ge4$ the bound $4\,\mathrm{opt}_k\le(1.9499+\varepsilon)\,\mathrm{opt}_k$ gives Theorem 1.2 of Part I with no extra facility, so the constants of the log-adaptive greedy algorithm are needed only for $\varepsilon<4$. The cost bound comes from the analysis of approximate local optima in Part II.
--
--   **Formalization Note** The algorithm reads the instance as the tuple $(n,m,k,\text{distance table})$. Costs and $\mathrm{opt}_k$ are real numbers.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Theorem 1.2. Lean source: `BCFGJPSSV26.Greedy.algLS_spec`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Algorithm.lean#L247-L285

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Core
public import Definitions.Def_BCFGJPSSV26_Greedy_Reduction_Scale
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_LocalSearch
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox
public import Definitions.Def_BCFGJPSSV26_Greedy_Algorithm

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

theorem algLS_spec {I : Instance} (hI : I.Valid) :
    I.IsCenterList (algLS (toRaw I)) ∧ (algLS (toRaw I)).length ≤ I.k ∧
      I.cost (I.centers (algLS (toRaw I))) ≤ 4 * I.opt I.k := by sorry

end BCFGJPSSV26.Greedy
end
