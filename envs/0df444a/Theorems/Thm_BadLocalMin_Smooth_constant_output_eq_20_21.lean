-- Prove2me | Theorems.Thm_BadLocalMin_Smooth_constant_output_eq_20_21
-- name    : BadLocalMin.Smooth.constant_output_eq_20_21
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:59.105531+00:00
-- url     : https://prove2.me/theorems/d8372cf4-cf40-4d3d-9641-93876f6e799f
-- title:
--   Eqs. (20)–(21), p. 19 — under (19) every hidden neuron outputs σ(a) and the network outputs σ(a)·1
-- statement:
--   Let $\Theta$ satisfy conditions (19a)–(19d), for an arbitrary activation $\sigma$, point $a$ and data $X$. Then every hidden pre-activation equals $a$ and every hidden post-activation equals $\sigma(a)$, whatever the input sample:
--   $$z_{h,i,n} = \sum_j w_{h,i,j}\, t_{h-1,j,n} + b_{h,i} = a, \qquad t_{h,i,n} = \sigma(a), \qquad h = 1, \dots, H,\ \forall i, n \qquad (20),$$
--   where $t_{0,j,n} = x_{j,n}$.
--   If moreover $W_{H+1}$ satisfies (19e) and $d_H \ge 1$, the network output is constant:
--   $$T_{H+1} = \frac{1}{d_H}\mathbf 1_{d_{H+1}\times d_H}\cdot \sigma(a\cdot \mathbf 1_{d_H \times N}) = \sigma(a)\cdot \mathbf 1_{d_{H+1}\times N} \qquad (21).$$
--
--   This identifies the loss at the constructed point: $E(\Theta) = \|\sigma(a)\mathbf 1 - Y\|_F^2 = \|\Delta Y\|_F^2$.
--
--   **Formalization Note.** Layers are indexed as in the paper ($1 \le h \le H$); neurons and samples are 0-indexed. The hypothesis $d_H \ge 1$ makes the average over the last hidden layer meaningful (with $d_H = 0$ the output would be $0$); it is implicit in (19e).
-- source:
--   Ding, Li & Sun, arXiv:1911.01413v3, p. 19, eqs. (19)–(21)

import Mathlib
import Definitions.Def_BadLocalMin_Smooth_Model

namespace BadLocalMin.Smooth

/-- Eqs. (20)–(21), p. 19. Under (19a)–(19d) every hidden pre-activation equals a and every
hidden post-activation equals σ(a) (eq. (20); paper layer h = k + 1 in the first clause, h = k
in the second); with (19e) and d_H ≥ 1 the network output is σ(a) · 1 (eq. (21)). -/
theorem constant_output_eq_20_21 (H N : ℕ) (d : ℕ → ℕ) (σ : ℝ → ℝ)
    (X : Fin (d 0) → Fin N → ℝ) (a : ℝ) (θ : Params d H) (hθ : Constr19ad σ a θ) :
    (∀ (k : ℕ) (hk : k < H) (i : Fin (d (k + 1))) (n : Fin N),
        (∑ j, θ.1 ⟨k, by omega⟩ i j * post σ X θ k (by omega) j n) + θ.2 ⟨k, hk⟩ i = a) ∧
    (∀ (k : ℕ) (hk1 : 1 ≤ k) (hkH : k ≤ H) (i : Fin (d k)) (n : Fin N),
        post σ X θ k hkH i n = σ a) ∧
      (Constr19e θ → 1 ≤ d H → ∀ i n, output σ X θ i n = σ a) := by sorry

end BadLocalMin.Smooth
