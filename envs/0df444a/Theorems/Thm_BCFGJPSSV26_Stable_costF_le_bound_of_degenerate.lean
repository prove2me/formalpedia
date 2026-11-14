-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_costF_le_bound_of_degenerate
-- name    : BCFGJPSSV26.Stable.costF_le_bound_of_degenerate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:47:55.697133+00:00
-- url     : https://prove2.me/theorems/f40a7343-eab1-4e2a-b18c-337544fc7bf8
-- title:
--   Degenerate cases $k=1$ or $\mathrm{opt}_k=0$: local search alone costs at most $(1.89+1000/N)\,\mathrm{opt}_k$
-- statement:
--   This lemma treats the two degenerate cases of the analysis of the algorithm for stable instances (Part II): $k=1$ and $\mathrm{opt}_k=0$. In both, an approximate local optimum already satisfies the final bound.
--
--   Let $I$ be a valid $k$-median instance: $n$ clients and $m\ge 1$ facilities with rational distances $d$ forming a pseudometric, and a number $k\ge 1$ of centers. For a set $F$ of facilities, $d(a,F)$ is the distance from a point $a$ to the nearest facility of $F$, $\mathrm{cost}(F)=\sum_{j} d(j,F)$ (sum over all clients $j$), and $\mathrm{opt}_k$ is the least cost of a nonempty set of at most $k$ facilities. Assume $k\le m$. Let $N\ge 201$ be an integer and let $S$ be an approximate local optimum for swaps of size $24N$ and threshold $1/(Nk)$: a set $S$ of facilities with $|S|=k$ such that every nonempty set $T$ of at most $k$ facilities with $|S\setminus T|\le 24N$ satisfies $\mathrm{cost}(T)\ge\bigl(1-\tfrac{1}{Nk}\bigr)\,\mathrm{cost}(S)$. If
--
--   $$k=1\qquad\text{or}\qquad \mathrm{opt}_k=0,$$
--
--   then
--
--   $$\mathrm{cost}(S)\;\le\;\Bigl(1.89+\frac{1000}{N}\Bigr)\,\mathrm{opt}_k .$$
--
--   The main analysis of Part II works under the standing hypotheses $k\ge 2$ and $\mathrm{opt}_k>0$ (they are needed, for instance, for stability to say something and for every optimal cluster to be nonempty). This lemma covers the remaining instances in the proof of the success probability of the algorithm: there the output of the local search, which is one of the candidates the algorithm compares, already costs at most $(1.89+1000/N)\,\mathrm{opt}_k\le(1.89+1000\,\varepsilon)\,\mathrm{opt}_k$, since the algorithm runs with $1/N<\varepsilon$.
--
--   **Formalization Note** Distances are rational and are cast to real numbers. In this part of the development the distance to the empty set of facilities is a finite number larger than all distances (it plays the role of the paper's $\infty$); on nonempty sets the cost is the cost of the model.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172). Lean source: `BCFGJPSSV26.Stable.costF_le_bound_of_degenerate`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Final/Combine.lean#L239-L264

module

public import Definitions.Def_BCFGJPSSV26_Stable_LSBound_NiceMaps
public import Definitions.Def_BCFGJPSSV26_Stable_Submod_Candidate
public import Definitions.Def_BCFGJPSSV26_Stable_WinWin
public import Definitions.Def_BCFGJPSSV26_Stable_Final_Combine

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Partition

variable {X : Ctx} {Λ₁ : List (Dummy X.I)} {w₁ : ClientWitness X Λ₁}
  {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} {w₂ : ClusterWitness w₁ LS' Λ₂}
  (Q : Partition w₂)

end Partition

theorem costF_le_bound_of_degenerate {I : Instance} (hv : I.Valid) (hk : I.k ≤ I.m) {N : ℕ}
    (hN : 201 ≤ N) {S : Finset (Fin I.m)} (hS : IsALO I (24 * N) (1 / (N * I.k)) S)
    (h : I.k = 1 ∨ I.opt I.k = 0) : I.costF S ≤ (1.89 + 1000 / N) * I.opt I.k := by sorry

end BCFGJPSSV26.Stable
end
