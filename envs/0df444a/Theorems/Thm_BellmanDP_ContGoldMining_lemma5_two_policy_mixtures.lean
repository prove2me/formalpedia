-- Prove2me | Theorems.Thm_BellmanDP_ContGoldMining_lemma5_two_policy_mixtures
-- name    : BellmanDP.ContGoldMining.lemma5_two_policy_mixtures
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T17:44:13.466203+00:00
-- url     : https://prove2.me/theorems/cf41796b-c270-48ca-a599-b6869f528e86
-- title:
--   Chapter VIII, Lemma 5 — mixtures of two policies occur only along $C_1 = 0$, $C_2 = 0$, $C_3 = 0$
-- statement:
--   Consider the three-choice continuous gold-mining process with positive rates $q_1, q_2, q_3, r_1, r_2, r_3, r_4$ and initial amounts $x_0, y_0 > 0$. Let $\varphi$ be an admissible control maximizing $f(\infty)$, or maximizing $f(T)$ for a finite horizon $T$, with trajectory $(x(t), y(t))$, and let $(a, b)$ be an interval with $0 \le a < b$ (and $b \le T$ in the finite case).
--
--   1. If $\varphi_1, \varphi_2 > 0$ and $\varphi_3 = 0$ almost everywhere on $(a, b)$ (a mixture of $A$ and $B$), then $C_1(x(t), y(t)) = 0$ for all $t \in (a, b)$ and, almost everywhere on $(a, b)$,
--   $$\varphi_1 = \frac{r_2}{r_1 + r_2},\qquad \varphi_2 = \frac{r_1}{r_1 + r_2}.$$
--   2. If $\varphi_1, \varphi_3 > 0$ and $\varphi_2 = 0$ almost everywhere on $(a, b)$ (a mixture of $A$ and $C$), then $C_2(x(t), y(t)) = 0$ on $(a, b)$ and, almost everywhere on $(a, b)$,
--   $$\varphi_1 = \frac{r_4 - r_3}{r_1 + r_4 - r_3},\qquad \varphi_3 = \frac{r_1}{r_1 + r_4 - r_3}.$$
--   3. If $\varphi_2, \varphi_3 > 0$ and $\varphi_1 = 0$ almost everywhere on $(a, b)$ (a mixture of $B$ and $C$), then $C_3(x(t), y(t)) = 0$ on $(a, b)$ and, almost everywhere on $(a, b)$,
--   $$\varphi_2 = \frac{r_3 - r_4}{r_2 + r_3 - r_4},\qquad \varphi_3 = \frac{r_2}{r_2 + r_3 - r_4}.$$
--
--   Here $C_1 = q_1 r_2 y - q_2 r_1 x$, $C_2 = q_1 r_4 y - (q_3 r_1 - q_1 r_3) x$, $C_3 = (q_3 r_2 - q_2 r_4) y - q_2 r_3 x$ (Eq. (13.2)). The proportions are those that keep the ratio $y/x$ constant on the corresponding line.
--
--   **Formalization Note** "Permissible only along $C_k = 0$" is read as: along an optimal control, a two-policy mixture on an interval keeps the state on that line and uses the stated proportions. When a denominator vanishes, the corresponding mixture cannot occur, so the conclusion holds vacuously. The book states the lemma for $T = \infty$ (§ 12) and derives it from the general-$T$ variation (12.4); the hypothesis covers both, optimality for $f(\infty)$ or for $f(T)$ with $T \ge b$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter VIII, § 14, Lemma 5, Eq. (3), p. 236

import Mathlib
import Definitions.Def_BellmanDP_ContGoldMining_Process
import Definitions.Def_BellmanDP_ContGoldMining_Switching

namespace BellmanDP.ContGoldMining

open MeasureTheory

/-- Bellman, *Dynamic Programming*, Ch. VIII, § 14, Lemma 5, p. 236: if an optimal control (for
`f(∞)`, the case § 12 considers, or for `f(T)` with `T ≥ b`) mixes exactly two decisions on an
interval `(a, b) ⊆ [0, ∞)`, then
(a) for `A` and `B`, the state stays on `C₁ = 0` and `φ₁ = r₂/(r₁ + r₂)`, `φ₂ = r₁/(r₁ + r₂)`;
(b) for `A` and `C`, it stays on `C₂ = 0` and `φ₁ = (r₄ − r₃)/(r₁ + r₄ − r₃)`,
`φ₃ = r₁/(r₁ + r₄ − r₃)`;
(c) for `B` and `C`, it stays on `C₃ = 0` and `φ₂ = (r₃ − r₄)/(r₂ + r₃ − r₄)`,
`φ₃ = r₂/(r₂ + r₃ − r₄)`. -/
theorem lemma5_two_policy_mixtures (P : Params) (hP : P.Positive) (x₀ y₀ : ℝ) (hx₀ : 0 < x₀)
    (hy₀ : 0 < y₀) (φ : Control) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hφ : IsOptimalInfty P x₀ y₀ φ ∨ ∃ T : ℝ, b ≤ T ∧ IsOptimalOn P x₀ y₀ T φ) :
    ((∀ᵐ t ∂(volume.restrict (Set.Ioo a b)), 0 < φ 0 t ∧ 0 < φ 1 t ∧ φ 2 t = 0) →
      (∀ t ∈ Set.Ioo a b, C₁ P (stateX P x₀ φ t) (stateY P y₀ φ t) = 0) ∧
      ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)),
        φ 0 t = P.r₂ / (P.r₁ + P.r₂) ∧ φ 1 t = P.r₁ / (P.r₁ + P.r₂)) ∧
    ((∀ᵐ t ∂(volume.restrict (Set.Ioo a b)), 0 < φ 0 t ∧ φ 1 t = 0 ∧ 0 < φ 2 t) →
      (∀ t ∈ Set.Ioo a b, C₂ P (stateX P x₀ φ t) (stateY P y₀ φ t) = 0) ∧
      ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)),
        φ 0 t = (P.r₄ - P.r₃) / (P.r₁ + P.r₄ - P.r₃) ∧ φ 2 t = P.r₁ / (P.r₁ + P.r₄ - P.r₃)) ∧
    ((∀ᵐ t ∂(volume.restrict (Set.Ioo a b)), φ 0 t = 0 ∧ 0 < φ 1 t ∧ 0 < φ 2 t) →
      (∀ t ∈ Set.Ioo a b, C₃ P (stateX P x₀ φ t) (stateY P y₀ φ t) = 0) ∧
      ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)),
        φ 1 t = (P.r₃ - P.r₄) / (P.r₂ + P.r₃ - P.r₄) ∧ φ 2 t = P.r₂ / (P.r₂ + P.r₃ - P.r₄)) := by sorry

end BellmanDP.ContGoldMining
