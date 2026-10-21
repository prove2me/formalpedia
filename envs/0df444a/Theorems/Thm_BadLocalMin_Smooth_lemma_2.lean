-- Prove2me | Theorems.Thm_BadLocalMin_Smooth_lemma_2
-- name    : BadLocalMin.Smooth.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:03.059763+00:00
-- url     : https://prove2.me/theorems/c16f3229-a738-42f6-856d-ae2fb30ee7f1
-- title:
--   Lemma 2, p. 21 — for each hidden layer h there is Θ satisfying (19a)–(19d) with the restricted perturbation directions (32) and (33)
-- statement:
--   Consider a fully connected network with $H \ge 1$ hidden layers and positive widths. Suppose $X$ satisfies Assumption 1, $\sigma$ satisfies Assumption 2 at $(a, \delta)$, and $\Delta Y \in \mathbb R^{d_{H+1}\times N}$ satisfies (23) with sign factor $[\sigma'(a)]^{H-1}\sigma''(a)$. Then for every hidden layer $h \in \{1, \dots, H\}$ there is a configuration $\Theta$ satisfying (19a)–(19d) and numbers $\delta^{(h)}, \gamma^{(h)} > 0$ such that for every $\Theta'$ within distance $\delta^{(h)}$ of $\Theta$
--   $$[\sigma'(a)]^{H-h}\Big\langle \Delta Y(i,:),\ (T_h)(j,:)(\Theta') - (T_h)(j,:)(\tilde\Theta')\Big\rangle \ \ge\ \gamma^{(h)}\,\big\|(T_h)(j,:)(\Theta') - (T_h)(j,:)(\tilde\Theta')\big\|_2^2 \qquad (32)$$
--   for all $1 \le i \le d_{H+1}$ and $1 \le j \le d_h$, where $\tilde\Theta'$ takes $W_1$ from $\Theta$ and everything else from $\Theta'$. Further, for every $\delta_0 > 0$ there is $\Theta'$ within distance $\delta_0$ of $\Theta$ with
--   $$[\sigma'(a)]^{H-h}\big\langle \Delta Y(i,:),\ (T_h)(j,:)(\Theta')\big\rangle > 0 \qquad (33)$$
--   for all $i, j$.
--
--   Lemma 2 at $h = H$ is the heart of the proof of Theorem 1: (32) gives the local-minimum property and (33) the descent direction.
--
--   **Formalization Note.** Three readings of the page are disclosed. (1) The paper assumes $Y$ satisfies (28); the statement assumes instead (23) for $\Delta Y = \sigma(a)\mathbf 1 - Y$, which (28) implies (see `output_data_eq_28`) and which is all the proof in Appendix G uses. (2) The printed range "$1 \le i \le d_{h+1}$" is read as $1 \le i \le d_{H+1}$, the rows of $\Delta Y$, as in Appendix G. (3) The paper's balls are Euclidean balls around the prefix $\Theta_{[1:h]}$; here they are sup-norm balls around the full $\Theta$. $T_h$ depends only on $\Theta_{[1:h]}$, the radii are existentially or universally quantified, and all norms on a finite-dimensional space are equivalent, so the statements are equivalent. Added hypotheses: $H \ge 1$, $d_0 \ge 1$, $d_h \ge 1$ for $1 \le h \le H+1$. Indices of neurons and samples are 0-based.
-- source:
--   Ding, Li & Sun, arXiv:1911.01413v3, p. 21, Lemma 2 (eqs. (32)–(33)); proof Appendix G, pp. 47–54

import Mathlib
import Definitions.Def_BadLocalMin_Smooth_Model

namespace BadLocalMin.Smooth

/-- Lemma 2 (p. 21). Hidden layer h of the paper is the Lean index h (1 ≤ h ≤ H); rows are
0-indexed. Hypothesis (28) on Y is replaced by its consequence (23) on ΔY (see
`output_data_eq_28`), with sign factor [σ′(a)]^{H−1}σ″(a). Balls are sup-norm balls in the
full parameter Θ. -/
theorem lemma_2 (H N : ℕ) (d : ℕ → ℕ) (σ : ℝ → ℝ) (X : Fin (d 0) → Fin N → ℝ)
    (a δ : ℝ) (hH : 1 ≤ H) (hd0 : 1 ≤ d 0) (hd : ∀ h, 1 ≤ h → h ≤ H + 1 → 1 ≤ d h)
    (hA1 : Assumption1 X) (hA2 : Assumption2At σ a δ)
    (dY : Fin (d (H + 1)) → Fin N → ℝ)
    (hdY : Cond23 X (deriv σ a ^ (H - 1) * deriv (deriv σ) a) dY) :
    ∀ (h : ℕ) (h1 : 1 ≤ h) (hh : h ≤ H), ∃ θ : Params d H, Constr19ad σ a θ ∧
      ∃ δh γh : ℝ, 0 < δh ∧ 0 < γh ∧
        (∀ θ' ∈ Metric.ball θ δh, ∀ (i : Fin (d (H + 1))) (j : Fin (d h)),
          γh * ∑ n, (post σ X θ' h hh j n - post σ X (tilde θ θ') h hh j n) ^ 2 ≤
            deriv σ a ^ (H - h) *
              ∑ n, dY i n * (post σ X θ' h hh j n - post σ X (tilde θ θ') h hh j n)) ∧
        (∀ δ0 : ℝ, 0 < δ0 → ∃ θ' ∈ Metric.ball θ δ0,
          ∀ (i : Fin (d (H + 1))) (j : Fin (d h)),
            0 < deriv σ a ^ (H - h) * ∑ n, dY i n * post σ X θ' h hh j n) := by sorry

end BadLocalMin.Smooth
