-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_algMain_spec
-- name    : BCFGJPSSV26.Greedy.algMain_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:39:53.301968+00:00
-- url     : https://prove2.me/theorems/ad475ee5-2a79-4e9d-ac8d-1b87d5a05787
-- title:
--   Guarantee of the main algorithm for fixed constants: cost at most $(\rho+10\delta)(1+\varepsilon')\,\mathrm{opt}_k$
-- statement:
--   This is the guarantee of the main algorithm behind Theorem 1.2 of Part I, for fixed constants and before their choice in terms of $\varepsilon$: on every instance it outputs few more than $k$ facilities, of cost at most $(\rho+10\delta)(1+\varepsilon')\,\mathrm{opt}_k$.
--
--   **Setting.** Fix rational constants $\delta,\varepsilon_g,\varepsilon'$ with $0<\delta\le\tfrac1{100}$, $\varepsilon_g=\tfrac{\delta}{10}$ and $0<\varepsilon'\le1$. Let $I$ be a $k$-median instance: $n$ clients and $m\ge1$ facilities in a pseudometric space with rational distances, and $k\ge1$. Write $\mathrm{cost}(S)=\sum_j\min_{i\in S}d(j,i)$, and $\mathrm{opt}_k$ for the least cost of a nonempty set of at most $k$ facilities. Let
--   $$B=\lfloor\log_2n\rfloor\cdot\lceil1/\delta^2\rceil,\qquad M=\frac{8n^2}{\varepsilon'}+1,\qquad R=\lceil1/\varepsilon_g^2\rceil\cdot\lceil\log_2\lceil5nM\rceil\rceil+1,$$
--   and $\rho=2-(\tfrac{153}{125}-1)^2=1.949824$.
--
--   **The algorithm.** The trivial solution consists of the nearest facility of every client (least index on ties), without repetitions. If $n=0$ the output is the facility $0$. If the trivial solution has at most $k+B$ facilities, it is the output. Otherwise, for every positive client–facility distance $\Lambda$, the core of the log-adaptive greedy algorithm runs on the input with distances $\min(d(j,i)/t+1,\ M)$, where $t=\varepsilon'\Lambda/n$; among its outputs that are nonempty lists of at most $k+6R$ distinct facilities, the one of least cost in $I$ is the output (the first one on ties; the facility $0$ if there is none).
--
--   **Statement.** The output $S$ satisfies:
--
--   1. $S$ is a nonempty list of distinct facilities of $I$;
--   2. $|S|\le k+B$, or: $B<n$, $n\ge2$ and $|S|\le k+6R$;
--   3. the cost bound
--   $$\mathrm{cost}(S)\ \le\ (\rho+10\delta)(1+\varepsilon')\cdot\mathrm{opt}_k .$$
--
--   Theorem 1.2 of Part I follows for $\varepsilon<4$ by choosing $\delta$ and $\varepsilon'=25\delta$ in terms of $\varepsilon$, so that the ratio is at most $1.9499+\varepsilon$ and both $B$ and $6R$ are at most $10^{10}\log n/\varepsilon^2$. The side conditions $B<n$ and $n\ge2$ of item 2 are what the bound on $6R$ needs. The scaling replaces the reduction of [CGLSS25, Lemma 1.4].
--
--   **Formalization Note** The algorithm reads the instance as the tuple $(n,m,k,\text{distance table})$. Costs and $\mathrm{opt}_k$ are real numbers; $\lfloor\log_2 0\rfloor=0$.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Theorem 1.2. Lean source: `BCFGJPSSV26.Greedy.algMain_spec`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Algorithm.lean#L89-L190

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

theorem algMain_spec {c : Consts} (hc : c.Good) {I : Instance} (hI : I.Valid) :
    I.IsCenterList (algMain c (toRaw I)) ∧
      ((algMain c (toRaw I)).length ≤ I.k + bcomp c I.n ∨
        (bcomp c I.n < I.n ∧ 2 ≤ I.n ∧ (algMain c (toRaw I)).length ≤ I.k + 6 * Rof c I.n)) ∧
      I.cost (I.centers (algMain c (toRaw I))) ≤
        (((ρ + 10 * c.δ) * (1 + c.εp) : ℚ) : ℝ) * I.opt I.k := by sorry

end BCFGJPSSV26.Greedy
end
