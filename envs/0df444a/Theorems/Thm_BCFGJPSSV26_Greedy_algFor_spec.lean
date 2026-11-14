-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_algFor_spec
-- name    : BCFGJPSSV26.Greedy.algFor_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:41:37.327755+00:00
-- url     : https://prove2.me/theorems/83978bb4-2897-475d-b8e2-0237339f96a5
-- title:
--   Guarantee of the algorithm of Theorem 1.2 (Part I) for a given $\varepsilon$
-- statement:
--   This is the guarantee part of Theorem 1.2 of Part I (Theorem 5.16 in full) for the explicit algorithm: for every $\varepsilon>0$ it opens at most $k+C\log n/\varepsilon^2$ facilities, with $C=10^{10}$, of cost at most $(1.9499+\varepsilon)\,\mathrm{opt}_k$.
--
--   **Setting.** Let $\varepsilon>0$ be a real number, and let $I$ be a $k$-median instance: $n$ clients and $m\ge1$ facilities in a pseudometric space with rational distances, and $k\ge1$. Write $\mathrm{cost}(S)=\sum_j\min_{i\in S}d(j,i)$, and $\mathrm{opt}_k$ for the least cost of a nonempty set of at most $k$ facilities.
--
--   **The algorithm for $\varepsilon$.** If $\varepsilon\ge4$, it is the large-$\varepsilon$ algorithm: the trivial solution (the nearest facility of every client) if it has at most $k$ facilities, and otherwise the local search of Part II with swaps of $24\cdot201$ facilities. If $\varepsilon<4$, it is the main algorithm with the constants $\delta$, $\varepsilon_g=\tfrac{\delta}{10}$ and $\varepsilon'=25\delta$, where $\delta$ is a fixed rational in $(\tfrac{\varepsilon}{200},\tfrac{\varepsilon}{100})$ for $\varepsilon\le1$ and $\delta=\tfrac1{100}$ for $1<\varepsilon<4$: the trivial solution if it is small enough, and otherwise the cheapest output of the core of the log-adaptive greedy algorithm (bid $[\alpha-1.224\,d]^+$, two solutions merged) over scaled copies of the instance. In both cases the output is the facility $0$ if $n=0$.
--
--   **Statement.** The output $S$ of the algorithm for $\varepsilon$ on $I$ satisfies:
--
--   1. $S$ is a nonempty list of distinct facilities of $I$;
--   2. $|S|\ \le\ k+10^{10}\cdot\dfrac{\ln n}{\varepsilon^2}$;
--   3. the cost bound
--   $$\mathrm{cost}(S)\ \le\ (1.9499+\varepsilon)\cdot\mathrm{opt}_k .$$
--
--   Together with the polynomial running time of the same algorithm, proved separately, this is Theorem 1.2 of Part I with the constant $C=10^{10}$ for all $\varepsilon$. The statement combines the guarantees of the main and the large-$\varepsilon$ algorithms with the bounds on the constants.
--
--   **Formalization Note** The algorithm reads the instance as the tuple $(n,m,k,\text{distance table})$. Costs and $\mathrm{opt}_k$ are real numbers, $\ln$ is the natural logarithm with $\ln0=0$, and for $\varepsilon\le1$ the number $\delta$ is obtained by choice, so the map from $\varepsilon$ to the algorithm is defined noncomputably, while for each $\varepsilon$ the algorithm is an explicit procedure.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Theorem 1.2 (Theorem 5.16 in full). Lean source: `BCFGJPSSV26.Greedy.algFor_spec`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Constants.lean#L253-L279

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Algorithm
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Definitions.Def_BCFGJPSSV26_Greedy_Constants

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Greedy

theorem algFor_spec {ε : ℝ} (hε : 0 < ε) {I : Instance} (hI : I.Valid) :
    I.IsCenterList (algFor ε (toRaw I)) ∧
      ((algFor ε (toRaw I)).length : ℝ) ≤ I.k + Cthm * Real.log I.n / ε ^ 2 ∧
      I.cost (I.centers (algFor ε (toRaw I))) ≤ (1.9499 + ε) * I.opt I.k := by sorry

end BCFGJPSSV26.Greedy
end
