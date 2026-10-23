-- Prove2me | Theorems.Thm_FairRentFPTAS_Approx_lemma_2
-- name    : FairRentFPTAS.Approx.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:35.920559+00:00
-- url     : https://prove2.me/theorems/eaf7579e-5355-4fb9-8d35-ea27d5936d3d
-- title:
--   Lemma 2, p. 8 — perturbation onto any maximum-weight perfect matching of F_w(p)
-- statement:
--   Let $\mathcal I$ be an instance with continuous, strictly decreasing piecewise-linear utilities, let $(\pi,p)$ be an envy-free solution, and let $\sigma$ be any maximum-weight perfect matching in the weighted first-choice graph $\mathcal F^w(p)$ (edge weights $\log\lambda^a_r$, $\lambda^a_r$ the left slope of $v_a(r,\cdot)$ at $p_r$). Then there is $\delta_0>0$ such that for every $\delta\in(0,\delta_0]$ there is a rent vector $q$ with $(\sigma,q)$ envy-free and
--   $$p_r-\delta\le q_r<p_r\qquad\text{for all rooms }r.$$
--
--   The lemma identifies which allocations survive a small uniform decrease of the rents; it drives the strict weight increase of Lemma 4.
--
--   **Formalization Note** As on p. 8, rents may be negative; below $0$ each utility continues its first linear piece.
-- source:
--   Arunachaleswaran, Barman & Rathi, Fully Polynomial-Time Approximation Schemes for Fair Rent Division, arXiv:1807.04163v1, p. 8, Lemma 2 (proof pp. 39–40)

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model

namespace FairRentFPTAS.Approx

/-- Lemma 2, p. 8 (proof pp. 39–40): if `(π, p)` is envy-free and `σ` is any maximum-weight
perfect matching of `F_w(p)`, then for every small enough `δ > 0` there is an envy-free solution
`(σ, q)` with `p_r − δ ≤ q_r < p_r` for every room. Prices of any sign are allowed. -/
theorem lemma_2 {n : ℕ} (J : Instance n) (hJ : Standing J) (π σ : Equiv.Perm (Fin n))
    (p : Fin n → ℝ) (hEF : IsEF J π p) (hσ : IsMaxWeightPM J p σ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ q : Fin n → ℝ, IsEF J σ q ∧ ∀ r, p r - δ ≤ q r ∧ q r < p r := by sorry

end FairRentFPTAS.Approx
