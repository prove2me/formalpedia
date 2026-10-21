-- Prove2me | Theorems.Thm_BadLocalMin_Smooth_output_data_eq_28
-- name    : BadLocalMin.Smooth.output_data_eq_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:04.381216+00:00
-- url     : https://prove2.me/theorems/86bc0e92-8b3e-4d28-bd82-e61c6aa23a53
-- title:
--   §6.1, eqs. (25)–(29), p. 20 — under Assumption 1, Y(i,:) = σ(a)·1 − Σ_l α_{i,l} u_l gives a ΔY satisfying (23)
-- statement:
--   Let $X \in \mathbb R^{d_0 \times N}$ satisfy Assumption 1 and let $\kappa \ne 0$ (in the paper $\kappa = [\sigma'(a)]^{H-1}\sigma''(a)$). Put $L = N - d_0^2/2 - d_0/2 - 1$. Then there are linearly independent vectors $\mathbf u_1, \dots, \mathbf u_L \in \mathbb R^N$ such that for all $l$ and all $j \ne j'$
--   $$\langle \mathbf u_l, \mathbf 1\rangle = 0,\quad \langle \mathbf u_l, X(j,:)\rangle = 0,\quad \langle \mathbf u_l, X(j,:)\circ X(j',:)\rangle = 0,\quad \langle \mathbf u_l, X(j,:)\circ X(j,:)\rangle > 0 \qquad (27a\text{–}d),$$
--   and such that for every number of rows $m$ and every choice of coefficients $\alpha_{i,l}$ having the same sign as $\kappa$, the matrix
--   $$\Delta Y(i,:) = \sum_{l=1}^{L} \alpha_{i,l}\,\mathbf u_l \qquad (29)$$
--   satisfies conditions (23a)–(23d) with sign factor $\kappa$. Equivalently, the output data $Y(i,:) = \sigma(a)\mathbf 1_N - \sum_l \alpha_{i,l}\mathbf u_l$ of (28) has $\Delta Y = \sigma(a)\mathbf 1 - Y$ satisfying (23).
--
--   This is the construction of the output matrix $Y$ in Theorem 1.
--
--   **Formalization Note.** $L$ is written $N - d_0(d_0+1)/2 - 1$ in ℕ; $d_0(d_0+1)$ is even and Assumption 1(a) gives $N > d_0(d_0+3)/2$, so no truncation occurs. "Same sign as $\kappa$" is $\kappa\,\alpha_{i,l} > 0$. The printed range "$1 \le j, j' \le N$" under (27) is read as $1 \le j, j' \le d_0$ (rows of $X$). Rows are 0-indexed.
-- source:
--   Ding, Li & Sun, arXiv:1911.01413v3, p. 20, §6.1, eqs. (25)–(29): 'It can be readily verified that such ΔY satisfies (23).'

import Mathlib
import Definitions.Def_BadLocalMin_Smooth_Model

namespace BadLocalMin.Smooth

/-- §6.1, eqs. (25)–(29), p. 20. Under Assumption 1 there are L = N − d₀(d₀+1)/2 − 1
linearly independent vectors u_l satisfying (27a)–(27d), and for every choice of coefficients
α_{i,l} of the same sign as κ (κ ≠ 0; in the paper κ = [σ′(a)]^{H−1}σ″(a)), the matrix
ΔY(i,:) = ∑_l α_{i,l} u_l of (29) satisfies (23). -/
theorem output_data_eq_28 (d0 N : ℕ) (X : Fin d0 → Fin N → ℝ) (hA1 : Assumption1 X)
    (κ : ℝ) (hκ : κ ≠ 0) :
    ∃ u : Fin (N - d0 * (d0 + 1) / 2 - 1) → Fin N → ℝ, LinearIndependent ℝ u ∧
      (∀ l, (∑ n, u l n = 0) ∧ (∀ j, ∑ n, u l n * X j n = 0) ∧
        (∀ j j', j ≠ j' → ∑ n, u l n * (X j n * X j' n) = 0) ∧
        (∀ j, 0 < ∑ n, u l n * (X j n * X j n))) ∧
      ∀ (m : ℕ) (α : Fin m → Fin (N - d0 * (d0 + 1) / 2 - 1) → ℝ),
        (∀ i l, 0 < κ * α i l) →
        Cond23 X κ (fun i n => ∑ l, α i l * u l n) := by sorry

end BadLocalMin.Smooth
