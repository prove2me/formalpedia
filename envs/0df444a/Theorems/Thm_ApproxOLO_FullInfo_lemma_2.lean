-- Prove2me | Theorems.Thm_ApproxOLO_FullInfo_lemma_2
-- name    : ApproxOLO.FullInfo.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:31.692216+00:00
-- url     : https://prove2.me/theorems/d2f7d02f-c424-40fd-8435-599dc3dff100
-- title:
--   Lemma 2, p. 7 — online gradient descent without feasibility: regret ≤ ‖x₁ − x‖²/(2Tη) + (η/(2T)) Σ‖f_t‖² against every x ∈ S
-- statement:
--   Let $\mathcal S\subset\mathbb R^d$ be convex and compact, $\eta>0$, $T\ge1$, and let $f_1,\dots,f_T\in\mathbb R^d$ be arbitrary. Consider plays $x_1,\dots,x_T$ of *online gradient descent without feasibility* (Algorithm 1): $x_1\in\mathcal S$, and for each $t$ the next point $x_{t+1}$ is an *infeasible projection* of $y_{t+1}$ onto $\mathcal S$, i.e.
--   $$\forall z\in\mathcal S:\quad\|z-x_{t+1}\|^2\le\|z-y_{t+1}\|^2,\tag{3}$$
--   where $y_{t+1}=x_t-\eta f_t$ for losses and $y_{t+1}=x_t+\eta f_t$ for payoffs. Then for every $x\in\mathcal S$,
--   $$\frac1T\sum_{t=1}^Tx_t\cdot f_t-\frac1T\sum_{t=1}^Tx\cdot f_t\le\frac1{2T\eta}\|x_1-x\|^2+\frac{\eta}{2T}\sum_{t=1}^T\|f_t\|^2\quad\text{(losses)},$$
--   $$\frac1T\sum_{t=1}^Tx\cdot f_t-\frac1T\sum_{t=1}^Tx_t\cdot f_t\le\frac1{2T\eta}\|x_1-x\|^2+\frac{\eta}{2T}\sum_{t=1}^T\|f_t\|^2\quad\text{(payoffs)}.$$
--
--   The points $x_2,\dots,x_T$ need not lie in $\mathcal S$; the classical regret bound of online gradient descent survives with this weaker projection, which is what makes approximate projections usable.
--
--   **Formalization Note** $\|\cdot\|$ is Euclidean. The infeasible-projection condition is required for $t=1,\dots,T-1$, the steps that produce played points $x_2,\dots,x_T$; Algorithm 1 also computes $x_{T+1}$, which is never played, so the statement covers every $T$-round run of Algorithm 1. $T\ge1$ is the paper's "$T$ rounds" with the factor $1/T$.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, p. 7, Lemma 2 (Algorithm 1, Eq. (3))

import Mathlib
import Definitions.Def_ApproxOLO_FullInfo_Model

namespace ApproxOLO.FullInfo

open Matrix

/-- **Lemma 2 (Online gradient descent without feasibility), Garber, arXiv:1709.03093v1, p. 7.**
Let `S ⊂ ℝ^d` be convex and compact, `η > 0`, `T ≥ 1`, and let `x_1 ∈ S`. If the plays
`x_1, …, x_T` of Algorithm 1 satisfy the infeasible-projection condition (3),
`‖z − x_{t+1}‖² ≤ ‖z − y_{t+1}‖²` for all `z ∈ S`, with `y_{t+1} = x_t − η f_t` (losses) resp.
`x_t + η f_t` (payoffs), then for every `x ∈ S`
`(1/T) Σ x_t · f_t − (1/T) Σ x · f_t ≤ (1/(2Tη)) ‖x_1 − x‖² + (η/(2T)) Σ ‖f_t‖²` (losses), and
`(1/T) Σ x · f_t − (1/T) Σ x_t · f_t ≤ (1/(2Tη)) ‖x_1 − x‖² + (η/(2T)) Σ ‖f_t‖²` (payoffs). -/
theorem lemma_2 {d : ℕ} (S : Set (Vec d)) (hS : Convex ℝ S) (hSc : IsCompact S)
    (eta : ℝ) (heta : 0 < eta) (T : ℕ) (hT : 1 ≤ T) (xs fs : ℕ → Vec d) (hx1 : xs 1 ∈ S) :
    ((∀ t, 1 ≤ t → t < T → ∀ z ∈ S,
        euclNorm (z - xs (t + 1)) ^ 2 ≤ euclNorm (z - (xs t - eta • fs t)) ^ 2) →
      ∀ x ∈ S,
        (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, xs t ⬝ᵥ fs t
            - (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t
          ≤ 1 / (2 * T * eta) * euclNorm (xs 1 - x) ^ 2
            + eta / (2 * T) * ∑ t ∈ Finset.Icc 1 T, euclNorm (fs t) ^ 2) ∧
    ((∀ t, 1 ≤ t → t < T → ∀ z ∈ S,
        euclNorm (z - xs (t + 1)) ^ 2 ≤ euclNorm (z - (xs t + eta • fs t)) ^ 2) →
      ∀ x ∈ S,
        (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t
            - (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, xs t ⬝ᵥ fs t
          ≤ 1 / (2 * T * eta) * euclNorm (xs 1 - x) ^ 2
            + eta / (2 * T) * ∑ t ∈ Finset.Icc 1 T, euclNorm (fs t) ^ 2) := by sorry

end ApproxOLO.FullInfo
