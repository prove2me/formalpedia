-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_alg_valid
-- name    : BCFGJPSSV26.Stable.alg_valid
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:47:09.735178+00:00
-- url     : https://prove2.me/theorems/f760be3d-b6a0-42c2-a2b9-ccab266e28c2
-- title:
--   Algorithm for stable instances (Part II, Theorem 1.1) — the output is always exactly $k$ distinct facilities
-- statement:
--   Validity of the output of the algorithm of Part II (arXiv:2610.17172), Theorem 1.1, for a fixed accuracy $1/N$: on every valid instance with $k\le m$, for every $L$ and every coin string, the algorithm outputs exactly $k$ distinct facilities.
--
--   **The algorithm for accuracy $1/N$.** Let $N\ge201$. On an instance $I$, a natural number $L$ and a string $r$ of coin flips, put $s=632NL$, $b=|\mathrm{enc}(I)|+7N$, $R=N^{200s+1}$ and $B=2^{e_1L}(|\mathrm{enc}(I)|+2)^{e_1}$ with $e_1=10^6N^2$. The algorithm runs the local search with swaps of size $24N$ and budget $B$; then $R$ trials, the $t$-th reading its own block of $6s+(20s+20)+k$ chunks of $b$ coins among the first $R\,(26s+20+k)\,b$ coins of $r$ (missing coins are read as $0$) and consisting, from the local-search solution, of the client sampling, the cluster sampling, a red–blue coloring of the kept centers, and the submodular step for every guess $p'\le s$, each guess returning a candidate list of facilities or being skipped. The local-search list and every candidate are made into lists of exactly $k$ distinct facilities (keep the facilities of the list, once each, append the other facilities in increasing order, keep the first $k$), and the output is the cheapest of them in exact rational arithmetic.
--
--   **Statement.** Let $N\ge201$, let $I$ be a valid $k$-median instance (a rational pseudometric on clients and $m\ge1$ facilities, $k\ge1$) with $k\le m$, let $L$ be any natural number and $r$ any finite string of coin flips. Then the output $A(I,L,r)$ of the algorithm is a list of facility indices such that
--
--   1. it is nonempty, has no repeated entries, and every entry is less than $m$;
--   2. its length is exactly $k$:
--   $$|A(I,L,r)|=k .$$
--
--   No stability assumption and no relation between $L$ and the instance is needed, and the coin string may have any length. This is the part of Theorem 1.1 that holds on every input ("always outputs exactly $k$ distinct facilities"); the approximation guarantee, which needs $\beta$-stability and $L\ge1/\beta$, is a separate statement about the same algorithm.
--
--   **Formalization Note** Facilities are the numbers $0,\dots,m-1$ and outputs are lists of numbers. The algorithm of the main theorem first computes a power of two $N\ge256$ from the rational accuracy $\varepsilon$ and then runs the algorithm described here.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Theorem 1.1 (validity of the output). Lean source: `BCFGJPSSV26.Stable.alg_valid`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/Main.lean#L65-L67

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

theorem alg_valid (P : Prm) (hv : I.Valid) (hk : I.k ≤ I.m) (L : ℕ) (r : List Bool) :
    I.IsCenterList (alg P ((I, L), r)) ∧ (alg P ((I, L), r)).length = I.k := by sorry

end BCFGJPSSV26.Stable
end
