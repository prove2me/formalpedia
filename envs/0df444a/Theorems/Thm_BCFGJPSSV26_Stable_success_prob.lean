-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_success_prob
-- name    : BCFGJPSSV26.Stable.success_prob
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:48:09.251324+00:00
-- url     : https://prove2.me/theorems/de9aa156-81b9-4dd4-ad15-8740c7b7e422
-- title:
--   Theorem 1.1 (Part II), for accuracy $1/N$ — cost at most $(1.89+1000/N)\,\mathrm{opt}$ with probability at least $1-1/N$
-- statement:
--   The approximation guarantee of Part II (arXiv:2610.17172), Theorem 1.1 (which is Theorem 1.3 of Part I), for the algorithm run with a fixed accuracy $1/N$: on a $\beta$-stable instance given with a number $L\ge1/\beta$, the output costs at most $(1.89+1000/N)$ times the optimum with probability at least $1-1/N$.
--
--   **The algorithm for accuracy $1/N$.** Let $N\ge201$. On an instance $I$, a natural number $L$ and a string $r$ of coin flips, put $s=632NL$, $b=|\mathrm{enc}(I)|+7N$, $R=N^{200s+1}$ and $B=2^{e_1L}(|\mathrm{enc}(I)|+2)^{e_1}$ with $e_1=10^6N^2$. The algorithm runs the local search with swaps of size $24N$ and budget $B$; then $R$ trials, the $t$-th reading its own block of $6s+(20s+20)+k$ chunks of $b$ coins among the first $R\,(26s+20+k)\,b$ coins of $r$ (missing coins are read as $0$) and consisting, from the local-search solution, of the client sampling, the cluster sampling, a red–blue coloring of the kept centers, and the submodular step for every guess $p'\le s$, each guess returning a candidate list of facilities or being skipped. The local-search list and every candidate are made into lists of exactly $k$ distinct facilities (keep the facilities of the list, once each, append the other facilities in increasing order, keep the first $k$), and the output is the cheapest of them in exact rational arithmetic.
--
--   **Statement.** Let $N\ge201$, and let $I$ be a valid $k$-median instance (a rational pseudometric on clients and $m\ge1$ facilities, $k\ge1$) with $k\le m$. Let $\beta>0$ be a real number such that $I$ is $\beta$-stable, i.e. $\mathrm{opt}_{k-1}\ge(1+\beta)\,\mathrm{opt}_k$ if $k\ge2$ (no condition if $k=1$), where $\mathrm{opt}_\ell$ is the least cost of a nonempty set of at most $\ell$ facilities. Let $L$ be a natural number with $L\ge1/\beta$, and let $T$ be a natural number with
--   $$T\ \ge\ N^{200s+1}\,(26s+20+k)\,\bigl(|\mathrm{enc}(I)|+7N\bigr),\qquad s=632NL .$$
--   Then, for a uniformly random string $r\in\{0,1\}^T$,
--   $$\Pr_r\Bigl[\ \mathrm{cost}\bigl(A(I,L,r)\bigr)\ \le\ \Bigl(1.89+\frac{1000}{N}\Bigr)\mathrm{opt}_k\ \Bigr]\ \ge\ 1-\frac1N .$$
--
--   This is the analytic core of Theorem 1.1. The main theorem follows by computing from a rational $\varepsilon\in(0,1/200)$ a power of two $N$ with $\varepsilon/512\le1/N<\varepsilon$, so that the bound becomes $(1.89+1000\varepsilon)\,\mathrm{opt}_k$ with probability at least $1-\varepsilon$, and by bounding the running time of the algorithm, uniformly in $N$, on multitape Turing machines.
--
--   **Formalization Note** The probability is the fraction of the coin strings of length exactly $T$; the algorithm reads only the first $N^{200s+1}(26s+20+k)\,b$ coins. Distances are rational and all costs are computed exactly. The cases $k=1$ and $\mathrm{opt}_k=0$ are covered: there the local search alone meets the bound.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Theorem 1.1 (Part I, arXiv:2610.18144, Theorem 1.3). Lean source: `BCFGJPSSV26.Stable.success_prob`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/Main.lean#L137-L222

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Trial
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_LocalSearch
public import Definitions.Def_BCFGJPSSV26_Stable_Time_Budget
public import Definitions.Def_BCFGJPSSV26_Combine_Analysis
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Main

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset Sampling

variable {I : Instance}

open Classical in

theorem success_prob (P : Prm) (hv : I.Valid) (hk : I.k ≤ I.m) {L : ℕ} {β : ℝ} (hβ : 0 < β)
    (hst : I.IsStable β) (hL : 1 / β ≤ L) {T : ℕ} (hT : Par.coinLen P.N I L ≤ T) :
    1 - 1 / (P.N : ℝ) ≤
      coinProb T fun r ↦ I.costF (I.centers (alg P ((I, L), r))) ≤ bound P I := by sorry

end BCFGJPSSV26.Stable
end
