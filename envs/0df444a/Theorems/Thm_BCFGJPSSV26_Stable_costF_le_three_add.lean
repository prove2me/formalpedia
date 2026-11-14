-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_costF_le_three_add
-- name    : BCFGJPSSV26.Stable.costF_le_three_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:47:44.8405+00:00
-- url     : https://prove2.me/theorems/d23e19cd-8c11-475a-a09b-7f6592efe411
-- title:
--   Corollary 1.5 (Part II) — local search is a $(3+100/N)$-approximation
-- statement:
--   This is Corollary 1.5 of Part II with explicit constants: an approximate local optimum for swaps of size $24N$ costs at most $(3+100/N)$ times the optimum.
--
--   Let $I$ be a valid $k$-median instance: $n$ clients and $m\ge 1$ facilities with rational distances $d$ forming a pseudometric, and a number $k\ge 1$ of centers. For a set $F$ of facilities, $d(a,F)$ is the distance from a point $a$ to the nearest facility of $F$, $\mathrm{cost}(F)=\sum_{j} d(j,F)$ (sum over all clients $j$), and $\mathrm{opt}_k$ is the least cost of a nonempty set of at most $k$ facilities. Assume $k\le m$. Let $N\ge 201$ be an integer and let $S$ be an approximate local optimum for swaps of size $24N$ and threshold $1/(Nk)$: a set $S$ of facilities with $|S|=k$ such that every nonempty set $T$ of at most $k$ facilities with $|S\setminus T|\le 24N$ satisfies $\mathrm{cost}(T)\ge\bigl(1-\tfrac{1}{Nk}\bigr)\,\mathrm{cost}(S)$. Then
--
--   $$\mathrm{cost}(S)\;\le\;\Bigl(3+\frac{100}{N}\Bigr)\,\mathrm{opt}_k .$$
--
--   The local search of the algorithm stops at such a set $S$. The bound follows from the refined local-search bound (Theorem 3.6) and yields $\mathrm{cost}(S)\le 4\,\mathrm{opt}_k$, which is all that the stability argument (Lemma 4.2, few unsynced clusters) and several error terms of the structural theorem use about the local search. With the fixed value $N=201$, the same local search also serves Part I for large $\varepsilon$.
--
--   **Formalization Note** Distances are rational and are cast to real numbers. In this part of the development the distance to the empty set of facilities is a finite number larger than all distances (it plays the role of the paper's $\infty$); on nonempty sets the cost is the cost of the model.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Corollary 1.5. Lean source: `BCFGJPSSV26.Stable.costF_le_three_add`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/LocalSearch/ThreeApprox.lean#L60-L99

module

public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_Refined
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {I : Instance}

theorem costF_le_three_add (hv : I.Valid) (hk : I.k ≤ I.m) {N : ℕ} (hN : 201 ≤ N)
    {S : Finset (Fin I.m)} (hS : IsALO I (24 * N) (1 / (N * I.k)) S) :
    I.costF S ≤ (3 + 100 / N) * I.opt I.k := by sorry

end BCFGJPSSV26.Stable
end
