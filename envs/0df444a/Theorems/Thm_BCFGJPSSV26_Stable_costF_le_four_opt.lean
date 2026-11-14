-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_costF_le_four_opt
-- name    : BCFGJPSSV26.Stable.costF_le_four_opt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:48:02.340784+00:00
-- url     : https://prove2.me/theorems/a2ad6325-1b62-4138-9464-e02d126df29e
-- title:
--   Local search is a $4$-approximation (weak form of Corollary 1.5, Part II)
-- statement:
--   This is the weak form of Corollary 1.5 of Part II that the rest of the analysis uses: an approximate local optimum costs at most $4$ times the optimum.
--
--   Let $I$ be a valid $k$-median instance: $n$ clients and $m\ge 1$ facilities with rational distances $d$ forming a pseudometric, and a number $k\ge 1$ of centers. For a set $F$ of facilities, $d(a,F)$ is the distance from a point $a$ to the nearest facility of $F$, $\mathrm{cost}(F)=\sum_{j} d(j,F)$ (sum over all clients $j$), and $\mathrm{opt}_k$ is the least cost of a nonempty set of at most $k$ facilities. Assume $k\le m$. Let $N\ge 201$ be an integer and let $S$ be an approximate local optimum for swaps of size $24N$ and threshold $1/(Nk)$: a set $S$ of facilities with $|S|=k$ such that every nonempty set $T$ of at most $k$ facilities with $|S\setminus T|\le 24N$ satisfies $\mathrm{cost}(T)\ge\bigl(1-\tfrac{1}{Nk}\bigr)\,\mathrm{cost}(S)$. Then
--
--   $$\mathrm{cost}(S)\;\le\;4\,\mathrm{opt}_k .$$
--
--   It weakens the bound $(3+100/N)\,\mathrm{opt}_k$ of Corollary 1.5. This is the only property of the local search used in the proof that few optimal clusters are unsynced (Lemma 4.2); it also converts error terms of the form $\varepsilon\,\mathrm{cost}(S)$ into $O(\varepsilon)\,\mathrm{opt}$ in the cost bound for the clusters with substitutes (structural theorem), and it settles the degenerate case $\mathrm{opt}_k=0$.
--
--   **Formalization Note** Distances are rational and are cast to real numbers. In this part of the development the distance to the empty set of facilities is a finite number larger than all distances (it plays the role of the paper's $\infty$); on nonempty sets the cost is the cost of the model.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Corollary 1.5 (weakened form). Lean source: `BCFGJPSSV26.Stable.costF_le_four_opt`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/LocalSearch/ThreeApprox.lean#L101-L109

module

public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_Refined
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {I : Instance}

theorem costF_le_four_opt (hv : I.Valid) (hk : I.k ≤ I.m) {N : ℕ} (hN : 201 ≤ N)
    {S : Finset (Fin I.m)} (hS : IsALO I (24 * N) (1 / (N * I.k)) S) :
    I.costF S ≤ 4 * I.opt I.k := by sorry

end BCFGJPSSV26.Stable
end
