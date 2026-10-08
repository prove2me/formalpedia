-- Prove2me | Theorems.Thm_BootRobust_Perf_event_eq_union_Cj
-- name    : BootRobust.Perf.event_eq_union_Cj
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:16.117175+00:00
-- url     : https://prove2.me/theorems/41aa42e7-aa3e-4c42-9c02-611de6ba5e78
-- title:
--   Proof of Theorem 6, p. 15 — bootstrap distributions lie in D_{n,n}, and E^n_D > c̄ iff D ∈ ∪_{j∈[n]} C_j
-- statement:
--   Let $1\le k\le n$, let $\emptyset=N^0\subseteq N^1\subseteq\dots\subseteq N^n=\Omega_n$ be a nested chain of neighbourhoods, $w>0$ weights, $\ell$ losses and $\bar c\in[-\infty,+\infty]$ a threshold.
--
--   1. The empirical distribution of any $n$ draws from $\Omega_n$ lies in $\mathcal D_{n,n}$.
--   2. For every $D\in\mathcal D_{n,n}$,
--   $$E^n_D>\bar c\iff D\in\bigcup_{j\in[n]}\mathcal C_j,\qquad \mathcal C_j=\{D\in\mathcal D^j_n:E^{n,j}_D>\bar c\}.$$
--
--   With $\bar c$ the robust budget, this identifies the disappointment event of Theorem 6 with the event that the bootstrap distribution falls in the union of the sets $\mathcal C_j$.
--
--   **Formalization Note** The page writes the event as $c_n(\bar z,D,x_0)>\bar c_n$, where the estimator $E^n_D[L(\bar z,y)|x=x_0]$ is meant; the latter is formalized. The threshold is arbitrary.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, proof of Theorem 6, p. 15, "C = {D ∈ D_n : c_n(z̄, D, x0) > c̄_n} = ∪_{j∈[n]} C_j"; D_bs[n] ∈ D_{n,n}, p. 11

import Mathlib
import Definitions.Def_BootRobust_Perf_Setting

namespace BootRobust.Perf

/-- Proof of Theorem 6, p. 15: the empirical distribution of `n` bootstrap draws is a bootstrap
distribution, and a bootstrap distribution `D` has estimate `E^n_D > c̄` exactly when it lies in
`⋃_{j ∈ [n]} C_j`. -/
theorem event_eq_union_Cj {ι : Type*} [Fintype ι] [DecidableEq ι] (n k : ℕ) (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hkn : k ≤ n) (N : ℕ → Finset ι) (hNmono : Monotone N) (hN0 : N 0 = ∅)
    (hNn : N n = Finset.univ) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (ℓ : ι → ℝ) (cbar : EReal) :
    (∀ ω : Fin n → ι, empDist ω ∈ Dnn n) ∧
      ∀ D ∈ Dnn n, (cbar < ((nominalEst n k N w ℓ D : ℝ) : EReal) ↔
        ∃ j ∈ Finset.Icc 1 n, D ∈ Cj n k N w ℓ cbar j) := by sorry

end BootRobust.Perf
