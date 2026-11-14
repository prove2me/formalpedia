-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_isALO_localSearch
-- name    : BCFGJPSSV26.Stable.isALO_localSearch
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:45:51.719973+00:00
-- url     : https://prove2.me/theorems/c37a542b-04a5-423b-b8b5-ad8c647b8454
-- title:
--   Local search (Part II, Section 3) — with a large enough budget the output is an approximate local optimum
-- statement:
--   Specification of the deterministic local search of Part II (arXiv:2610.17172), Section 3, with swaps of size $24N$ and the approximate stopping rule of Theorem 3.6: when its budget is large enough, its output is an approximate local optimum.
--
--   **Setting.** Let $I$ be a valid $k$-median instance (clients and $m$ facilities with a rational pseudometric $d$, $k\ge1$, $m\ge1$) with $k\le m$, and let $|\mathrm{enc}(I)|$ be the length of its binary encoding. The cost of a set of facilities is the sum over the clients of the distance to the nearest facility of the set.
--
--   **The local search.** Given an integer $N$ and a budget $B$, the local search keeps a list of $k$ distinct facilities, initially the facilities $0,\dots,k-1$. A *swap* is a tuple of $24N$ numbers $x\lt km$, applied entry by entry: the facility at position $\lfloor x/m\rfloor$ of the list is replaced by the facility $x\bmod m$, unless the latter is already in the list. The swaps are enumerated in a fixed order, the tuples being built one coordinate at a time with at most $B$ of them kept at each stage (so all $(km)^{24N}$ are present when $B\ge(km)^{24N}$). One step applies the first enumerated swap whose result $T$ satisfies, in exact rational arithmetic, $\mathrm{cost}(T)<\bigl(1-\tfrac{1}{Nk}\bigr)\mathrm{cost}(S)$ for the current list $S$, and does nothing if there is none. The output is the list after $B$ steps.
--
--   **Statement.** Let $N\ge1$ and let $B$ be a natural number with
--   $$B\ \ge\ (km)^{24N}\qquad\text{and}\qquad B\ \ge\ 2Nk\,|\mathrm{enc}(I)|+2 .$$
--   Then the set $S$ of facilities output by the local search with parameters $N$ and $B$ satisfies $|S|=k$, and for every nonempty set $T$ of at most $k$ facilities with $|S\setminus T|\le24N$,
--   $$\Bigl(1-\frac{1}{Nk}\Bigr)\mathrm{cost}(S)\ \le\ \mathrm{cost}(T).$$
--
--   The set $S$ produced here is the local-search solution of the whole analysis of Part II: approximate local optimality is the only property of $S$ among the standing hypotheses, and it gives the refined local-search bound (Theorem 3.6) and, for $N\ge201$, $\mathrm{cost}(S)\le(3+100/N)\,\mathrm{opt}_k$ (Corollary 1.5). The algorithm of Theorem 1.1 runs the local search with the budget $2^{e_1L}(|\mathrm{enc}(I)|+2)^{e_1}$, $e_1=10^6N^2$, which satisfies both conditions.
--
--   **Formalization Note** The first condition on $B$ ensures that all swaps are tried, the second that the search has stopped improving after $B$ steps. The local search only tries sets of exactly $k$ facilities; the conclusion covers all nonempty sets of at most $k$ facilities.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Section 3 (the local search, with the stopping rule of Theorem 3.6). Lean source: `BCFGJPSSV26.Stable.isALO_localSearch`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/LocalSearch.lean#L546-L596

module

public import Definitions.Def_BCFGJPSSV26_Stable_Params
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox
public import Definitions.Def_BuhaiPapers_Background_Tuples
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_LocalSearch

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Tuples Encoding

variable {I : Instance}

theorem isALO_localSearch (hv : I.Valid) (hk : I.k ≤ I.m) {N B : ℕ} (hN : 1 ≤ N)
    (hB₁ : (I.k * I.m) ^ Par.p N ≤ B) (hB₂ : 2 * N * I.k * (encInstance I).length + 2 ≤ B) :
    IsALO I (Par.p N) (1 / (N * I.k)) (I.centers (localSearch N (toRaw I) B)) := by sorry

end BCFGJPSSV26.Stable
end
