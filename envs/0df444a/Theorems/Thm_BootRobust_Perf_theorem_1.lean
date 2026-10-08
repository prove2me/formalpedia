-- Prove2me | Theorems.Thm_BootRobust_Perf_theorem_1
-- name    : BootRobust.Perf.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:34.362946+00:00
-- url     : https://prove2.me/theorems/bb490466-31bc-4994-98cb-a971a7d2f337
-- title:
--   Theorem 1, p. 11 — on bootstrap distributions the estimator (18) is the maximum of the partial estimators (22)
-- statement:
--   Let $1\le k\le n$, let $\emptyset=N^0\subseteq N^1\subseteq\dots\subseteq N^n=\Omega_n$ be a nested chain of neighbourhoods, $w>0$ weights and $\ell$ losses. For every bootstrap distribution $D\in\mathcal D_{n,n}$:
--
--   1. for each $j\in[n]$ with $D\in\mathcal D^j_n$, the estimator (18) equals the partial estimator, $E^n_D=E^{n,j}_D$;
--   2. $$E^n_D=\max_{j\in[n]}E^{n,j}_D .$$
--
--   Theorem 1 turns the estimator, which selects a neighbourhood depending on $D$, into a maximum of $n$ partial estimators, each defined by a linear program. The robust budget (26) and the proof of Theorem 6 rest on this characterization.
--
--   **Formalization Note** The loss enters as a vector $\ell_i=L(z,\bar y)$, so the statement holds for every decision $z$. The maximum is a supremum in `EReal`; the partial estimators off their domains are $-\infty$.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, Theorem 1, p. 11 (proof in B.1, pp. 26–27)

import Mathlib
import Definitions.Def_BootRobust_Perf_Setting

namespace BootRobust.Perf

/-- Theorem 1, p. 11: on bootstrap distributions `D ∈ D_{n,n}` the estimator (18) equals the
partial estimator `E^{n,j}_D` whenever `D ∈ D^j_n`, and is the maximum over `j ∈ [n]` of the
partial estimators (22). -/
theorem theorem_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (n k : ℕ) (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hkn : k ≤ n) (N : ℕ → Finset ι) (hNmono : Monotone N) (hN0 : N 0 = ∅)
    (hNn : N n = Finset.univ) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (ℓ : ι → ℝ) (D : ι → ℝ)
    (hD : D ∈ Dnn n) :
    (∀ j ∈ Finset.Icc 1 n, D ∈ Dj n k N j →
        ((nominalEst n k N w ℓ D : ℝ) : EReal) = partialEst n k N w ℓ j D) ∧
      ((nominalEst n k N w ℓ D : ℝ) : EReal) = ⨆ j ∈ Finset.Icc 1 n, partialEst n k N w ℓ j D := by sorry

end BootRobust.Perf
