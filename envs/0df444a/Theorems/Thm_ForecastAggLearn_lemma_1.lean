-- Prove2me | Theorems.Thm_ForecastAggLearn_lemma_1
-- name    : ForecastAggLearn.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:18.692503+00:00
-- url     : https://prove2.me/theorems/c7a546b5-0045-491a-a6cf-e7ce5c7503c3
-- title:
--   Lemma 1 — online gradient descent on the losses (4) has regret $O(WZ\sqrt T)$
-- statement:
--   Let $T\ge1$, $Z>0$, $W>0$, and let $(\tilde z_t,\omega_t,\tilde\mu_t)_{t\in[T]}$ be a sequence with $\|\tilde z_t\|\le Z$; let $\overline L_t$ be the loss (4) for $(\tilde z_t,\omega_t,\tilde\mu_t)$. Run **online gradient descent** (6):
--
--   $$
--   h_1=0_n,\qquad h_{t+1}=\Pi_{\|\cdot\|\le W}\Bigl[h_t-\sqrt{\tfrac{4W^2}{Z^2T}}\,\nabla\overline L_t(h_t)\Bigr],\qquad \Pi_{\|\cdot\|\le W}[z]=W\frac{z}{\max\{\|z\|,W\}} .
--   $$
--
--   Then for every $h\in\mathbb R^n$ with $\|h\|\le W$,
--
--   $$
--   \sum_{t=1}^T\overline L_t(h_t)-\sum_{t=1}^T\overline L_t(h)\le 2WZ\sqrt T ,
--   $$
--
--   so $\sum_t\overline L_t(h_t)-\min_{\|h\|\le W}\sum_t\overline L_t(h)=O(WZ\sqrt T)$.
--
--   This is the learning step of the paper: with $W\ge\|h^*\|$ it bounds the regret against the optimal aggregation on non-extreme periods.
--
--   **Formalization Note** Periods are 0-based ($h_1$ is `h 0`). $\nabla$ is Mathlib's `gradient`. The projection is the printed formula. The general projected online gradient method with this step and bound $GD\sqrt T$ ($D=2W$, $G=Z$) is the platform theorem `OracleRO.DualSubgrad.lemma_1`, included as a reference item.
--
--   Differences from the source:
--   - generalization: O(WZ√T) → ≤ 2WZ√T; reason: an explicit constant implies the O-bound; 2 is the constant of the standard analysis with diameter 2W and gradient bound Z
--   - encoding: Σ L̄_t(h_t) − min_{‖h‖≤W} Σ L̄_t(h) → Σ L̄_t(h_t) − Σ L̄_t(h) for every h with ‖h‖ ≤ W; reason: the minimum of a continuous function on the compact ball is attained, so the two bounds are the same
--   - reading: ∇L̄(h_t) in (6) → the gradient of L̄_t at h_t; reason: the step at time t uses the loss of period t, as in the standard algorithm cited (Hazan 2016)
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, Lemma 1, eq. (6), p.18

import Mathlib
import Definitions.Def_ForecastAggLearn_barL

namespace ForecastAggLearn

/-- **Lemma 1 (Online Gradient Descent).**
Babichenko, Garber, arXiv:1802.07107v1, Lemma 1, p.18: for a sequence `(z̃_t, ω_t, µ̃_t)_{t∈[T]}`
with `‖z̃_t‖ ≤ Z`, `Z > 0`, the losses `L̄_t` of Eq. (4), and the iterates
`h_1 ← 0_n; h_{t+1} ← Π_{‖·‖≤W}[h_t − √(4W²/(Z²T)) ∇L̄_t(h_t)]` (6), where
`Π_{‖·‖≤W}[z] := W z / max{‖z‖, W}` and `W > 0`,
`Σ_{t=1}^T L̄_t(h_t) − min_{‖h‖≤W} Σ_{t=1}^T L̄_t(h) = O(W Z √T)`.

Here the regret against every `h` with `‖h‖ ≤ W` is at most `2 W Z √T`.

**Formalization Note.** Periods are 0-based: the paper's `h_1` is `h 0` and its period `t` is
`t − 1`. `∇` is Mathlib's `gradient`. The `min` over the ball (attained, by continuity and
compactness) is replaced by "for every `h` in the ball", which is the same bound. The `O(·)` is
made explicit with the constant `2`, the constant of the standard analysis (diameter `2W`,
gradient bound `Z`). -/
theorem lemma_1 {n T : ℕ} (hT : 0 < T) (z : ℕ → EuclideanSpace ℝ (Fin n)) (ω : ℕ → Bool)
    (μt : ℕ → ℝ) (Z W : ℝ) (hZ : 0 < Z) (hW : 0 < W) (hz : ∀ t < T, ‖z t‖ ≤ Z)
    (h : ℕ → EuclideanSpace ℝ (Fin n)) (h0 : h 0 = 0)
    (hstep : ∀ t < T, h (t + 1) =
      let v := h t - Real.sqrt (4 * W ^ 2 / (Z ^ 2 * T)) •
        gradient (barL (z t) (μt t) (ω t)) (h t)
      (W / max ‖v‖ W) • v) :
    ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ W →
      ∑ t ∈ Finset.range T, barL (z t) (μt t) (ω t) (h t) -
          ∑ t ∈ Finset.range T, barL (z t) (μt t) (ω t) u ≤
        2 * W * Z * Real.sqrt T := by sorry

end ForecastAggLearn
