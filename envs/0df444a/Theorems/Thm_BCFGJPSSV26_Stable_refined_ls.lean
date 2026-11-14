-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_refined_ls
-- name    : BCFGJPSSV26.Stable.refined_ls
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:47:25.377809+00:00
-- url     : https://prove2.me/theorems/dedfc12a-a40e-469a-a4b9-f48b35b09e3e
-- title:
--   Theorem 3.6 (Part II) — refined local-search bound for cross-free assignments
-- statement:
--   This is the refined local-search bound, Theorem 3.6 of Part II: an approximate local optimum is compared with a benchmark solution through two assignments of the clients whose clusterings are cross-free.
--
--   Let $I$ be a valid $k$-median instance: $n$ clients and $m\ge 1$ facilities with rational distances $d$ forming a pseudometric, and a number $k\ge 1$ of centers. For a set $F$ of facilities, $d(a,F)$ is the distance from a point $a$ to the nearest facility of $F$, $\mathrm{cost}(F)=\sum_{j} d(j,F)$ (sum over all clients $j$), and $\mathrm{opt}_k$ is the least cost of a nonempty set of at most $k$ facilities. Write $D$ for the set of all clients. Let $N\ge 200$ be an integer and let $S$ be an approximate local optimum for swaps of size $24N$ and threshold $1/(Nk)$: a set $S$ of facilities with $|S|=k$ such that every nonempty set $T$ of at most $k$ facilities with $|S\setminus T|\le 24N$ satisfies $\mathrm{cost}(T)\ge\bigl(1-\tfrac{1}{Nk}\bigr)\,\mathrm{cost}(S)$. Let $B$ be a set of facilities, $\mu_A:D\to S$ and $\mu_B:D\to B$ assignments of the clients, and $D_0\subseteq D$, such that
--
--   1. $|B|+|\mu_A(D\setminus D_0)|\le k$;
--   2. $\mu_A$ and $\mu_B$ are *cross-free with respect to $D_0$* (Definition 3.5): let $A'$ be the set of $c\in S$ with $\mu_A^{-1}(c)\subseteq D_0$ and $\hat D_0=\mu_A^{-1}(A')$; then for every $c\in A'$ and every facility $c'$, the sets $\mu_A^{-1}(c)$ and $\mu_B^{-1}(c')\cap\hat D_0$ are disjoint or one of them contains the other.
--
--   Then, with $\mathrm{cost}_\mu(E)=\sum_{j\in E}d(j,\mu(j))$ and $\mathrm{cost}_S(E)=\sum_{j\in E}d(j,S)$,
--
--   $$\mathrm{cost}(S)\;\le\;\mathrm{cost}_{\mu_B}(D_0)+\bigl(\mathrm{cost}_{\mu_A}(D)-\mathrm{cost}_S(D_0)\bigr)+\frac{10}{N}\bigl(\mathrm{cost}_{\mu_A}(D)+\mathrm{cost}_{\mu_B}(D_0)\bigr).$$
--
--   The bound is used twice. With $B$ an optimal solution, $D_0=D$, $\mu_B$ the nearest optimal center and $\mu_A$ the center of $S$ nearest to it, it gives that local search is a $(3+100/N)$-approximation (Corollary 1.5). With the cross-free maps of Lemma 3.7 built from the structural partition, it gives the nuanced local-search bound (Theorem 3.8).
--
--   **Formalization Note** Distances are rational and are cast to real numbers. In this part of the development the distance to the empty set of facilities is a finite number larger than all distances (it plays the role of the paper's $\infty$); on nonempty sets the cost is the cost of the model. The paper's $O(\varepsilon)$ factor is the explicit $10/N$.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Theorem 3.6. Lean source: `BCFGJPSSV26.Stable.refined_ls`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/LocalSearch/Refined.lean#L128-L459

module

public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_Defs
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_StarForest
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_Refined

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {I : Instance}

theorem refined_ls (hv : I.Valid) {N : ℕ} (hN : 200 ≤ N) {S B : Finset (Fin I.m)}
    (hS : IsALO I (24 * N) (1 / (N * I.k)) S) {μA μB : Fin I.n → Fin I.m}
    (hA : ∀ j, μA j ∈ S) (hB : ∀ j, μB j ∈ B) {D₀ : Finset (Fin I.n)}
    (hsize : B.card + (D₀ᶜ.image μA).card ≤ I.k) (hcf : CrossFreeWrt I S μA μB D₀) :
    I.costF S ≤ I.costMap μB D₀ + (I.costMap μA univ - I.costOn S D₀) +
      10 / N * (I.costMap μA univ + I.costMap μB D₀) := by sorry

end BCFGJPSSV26.Stable
end
