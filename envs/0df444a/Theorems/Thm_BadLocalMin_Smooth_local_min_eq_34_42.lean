-- Prove2me | Theorems.Thm_BadLocalMin_Smooth_local_min_eq_34_42
-- name    : BadLocalMin.Smooth.local_min_eq_34_42
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:03.358975+00:00
-- url     : https://prove2.me/theorems/48d88404-7f94-49b2-bee4-48767e5413be
-- title:
--   §6.2, eqs. (34)–(42), pp. 21–23 — Θ satisfying (19) and (32) at h = H is a local minimum of E
-- statement:
--   Let $H \ge 1$ and $d_H \ge 1$, let $\Delta Y \in \mathbb R^{d_{H+1}\times N}$ have rows summing to zero ($\langle \Delta Y(i,:), \mathbf 1\rangle = 0$, condition (23a)), and set $Y = \sigma(a)\mathbf 1_{d_{H+1}\times N} - \Delta Y$. Let $\Theta$ satisfy (19a)–(19e) and suppose that its last hidden layer obeys (32): there are $\delta^{(H)}, \gamma^{(H)} > 0$ such that for every $\Theta'$ within distance $\delta^{(H)}$ of $\Theta$ and all $i, j$
--   $$\Big\langle \Delta Y(i,:),\ (T_H)(j,:)(\Theta') - (T_H)(j,:)(\tilde\Theta')\Big\rangle \ \ge\ \gamma^{(H)}\big\|(T_H)(j,:)(\Theta') - (T_H)(j,:)(\tilde\Theta')\big\|_2^2 .$$
--   Then $\Theta$ is a local minimum of the empirical loss $E(\Theta) = \|Y - T_{H+1}(\Theta)\|_F^2$.
--
--   Together with Lemma 2 (at $h = H$, where the factor $[\sigma'(a)]^{H-h}$ equals $1$), this is §6.2 of the paper: the configuration built from Lemma 2 and (19e) is a local minimum.
--
--   **Formalization Note.** Distances are sup-norm distances on the parameter space; the conclusion is Mathlib's `IsLocalMin` for the product topology. Neurons and samples are 0-indexed.
-- source:
--   Ding, Li & Sun, arXiv:1911.01413v3, pp. 21–23, §6.2, eqs. (34)–(42): 'Thus, (37b) is also satisfied, and hence Θ is indeed a local minimum.'

import Mathlib
import Definitions.Def_BadLocalMin_Smooth_Model

namespace BadLocalMin.Smooth

/-- §6.2, eqs. (34)–(42), pp. 21–23. A configuration Θ satisfying (19a)–(19e) whose last
hidden layer obeys (32) (at h = H, where the sign factor is 1) is a local minimum of E for the
output data Y = σ(a) · 1 − ΔY, provided ΔY satisfies (23a). -/
theorem local_min_eq_34_42 (H N : ℕ) (d : ℕ → ℕ) (σ : ℝ → ℝ) (X : Fin (d 0) → Fin N → ℝ)
    (a : ℝ) (hH : 1 ≤ H) (hdH : 1 ≤ d H) (dY : Fin (d (H + 1)) → Fin N → ℝ)
    (hdY : ∀ i, ∑ n, dY i n = 0) (θ : Params d H)
    (h19ad : Constr19ad σ a θ) (h19e : Constr19e θ)
    (h32 : ∃ δH γH : ℝ, 0 < δH ∧ 0 < γH ∧
      ∀ θ' ∈ Metric.ball θ δH, ∀ (i : Fin (d (H + 1))) (j : Fin (d H)),
        γH * ∑ n, (post σ X θ' H le_rfl j n - post σ X (tilde θ θ') H le_rfl j n) ^ 2 ≤
          ∑ n, dY i n * (post σ X θ' H le_rfl j n - post σ X (tilde θ θ') H le_rfl j n)) :
    IsLocalMin (loss σ X (fun i n => σ a - dY i n)) θ := by sorry

end BadLocalMin.Smooth
