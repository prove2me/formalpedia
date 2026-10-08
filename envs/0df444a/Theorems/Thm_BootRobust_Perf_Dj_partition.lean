-- Prove2me | Theorems.Thm_BootRobust_Perf_Dj_partition
-- name    : BootRobust.Perf.Dj_partition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:23.302906+00:00
-- url     : https://prove2.me/theorems/653c44d7-73a2-41c9-84e6-2e71940e35c9
-- title:
--   B.1, p. 26 — the sets D^j_{n,n} = D^j_n ∩ D_{n,n}, j ∈ [n], partition D_{n,n}
-- statement:
--   Let $1\le k\le n$ and let $\emptyset=N^0\subseteq N^1\subseteq\dots\subseteq N^n=\Omega_n$ be a nested chain of neighbourhoods. Write $\mathcal D^j_{n,n}=\mathcal D^j_n\cap\mathcal D_{n,n}$. Then
--
--   1. $\mathcal D^j_{n,n}\cap\mathcal D^{j'}_{n,n}=\emptyset$ for all $j\neq j'$ in $[n]=\{1,\dots,n\}$, and
--   2. $$\bigcup_{j\in[n]}\mathcal D^j_{n,n}=\mathcal D_{n,n}.$$
--
--   Every bootstrap distribution has a unique smallest neighbourhood holding at least $k$ of its $n$ observations; this partition is what lets the estimator be written as a maximum of partial estimators (Theorem 1).
--
--   **Formalization Note** The chain abstracts Definition 2: under its discrimination property the neighbourhoods $N^j_n(x_0)$ are nested, $N^n_n(x_0)$ holds all $n$ observations, and $N^0=\emptyset$ is the convention for $N^{j-1}$ at $j=1$.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, B.1 (proof of Theorem 1), p. 26, "Formally, D^j_{n,n} ∩ D^{j′}_{n,n} = ∅ …"

import Mathlib
import Definitions.Def_BootRobust_Perf_Setting

namespace BootRobust.Perf

/-- B.1, p. 26: the sets `D^j_{n,n} = D^j_n ∩ D_{n,n}`, `j ∈ [n]`, are pairwise disjoint and
cover `D_{n,n}`. -/
theorem Dj_partition {ι : Type*} [Fintype ι] [DecidableEq ι] (n k : ℕ) (hk : 1 ≤ k)
    (hkn : k ≤ n) (N : ℕ → Finset ι) (hNmono : Monotone N) (hN0 : N 0 = ∅)
    (hNn : N n = Finset.univ) :
    (∀ j ∈ Finset.Icc 1 n, ∀ j' ∈ Finset.Icc 1 n, j ≠ j' →
        Disjoint (Dj n k N j ∩ Dnn n) (Dj n k N j' ∩ Dnn n)) ∧
      (⋃ j ∈ Finset.Icc 1 n, Dj n k N j ∩ Dnn n) = Dnn n := by sorry

end BootRobust.Perf
