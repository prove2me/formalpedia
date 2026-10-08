-- Prove2me | Theorems.Thm_BellmanDP_ContGoldMining_lemma4_no_triple_mixture
-- name    : BellmanDP.ContGoldMining.lemma4_no_triple_mixture
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T17:43:20.4716+00:00
-- url     : https://prove2.me/theorems/60c3f534-d6b4-4f72-81e8-4b51ab42b34b
-- title:
--   Chapter VIII, Lemma 4 — no optimal policy mixes A, B and C
-- statement:
--   Consider the three-choice continuous gold-mining process with positive rates $q_1, q_2, q_3, r_1, r_2, r_3, r_4$ and initial amounts $x_0, y_0 > 0$. Assume, as § 13 does, that the lines $C_2 = 0$ and $C_3 = 0$ lie in the open positive quadrant, that is,
--   $$q_1 r_3 < q_3 r_1 \qquad\text{and}\qquad q_2 r_4 < q_3 r_2,$$
--   and that $D = q_1 r_2 r_3 + q_2 r_1 r_4 - q_3 r_1 r_2 \ne 0$. Let $\varphi$ be an admissible control maximizing $f(\infty)$, or maximizing $f(T)$ for a finite horizon $T$. Then there is no interval $(a, b)$ with $0 \le a < b$ (and $b \le T$ in the finite case) on which
--   $$\varphi_1(t) > 0,\quad \varphi_2(t) > 0,\quad \varphi_3(t) > 0 \qquad\text{for almost every } t \in (a, b).$$
--
--   In words: an optimal policy never contains a mixture of the $A$-, $B$- and $C$-policies. Together with Lemma 5 this reduces the candidate optimal policies to pure policies and mixtures of two decisions along fixed rays.
--
--   **Formalization Note** "A mixture" is read as an interval of positive length on which all three proportions are positive almost everywhere. The line $C_1 = 0$ always lies in the positive quadrant; the two inequalities are the book's assumption for the other two lines. The book states the lemma for $T = \infty$ (§ 12 considers only that case) and derives it from the variation (12.4), written for a general $T$; the hypothesis covers both, optimality for $f(\infty)$ or for $f(T)$ with $T \ge b$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter VIII, § 14, Lemma 4, p. 235 (with the assumptions of § 13, p. 235)

import Mathlib
import Definitions.Def_BellmanDP_ContGoldMining_Process
import Definitions.Def_BellmanDP_ContGoldMining_Switching

namespace BellmanDP.ContGoldMining

open MeasureTheory

/-- Bellman, *Dynamic Programming*, Ch. VIII, § 14, Lemma 4, p. 235: assuming, as § 13 does,
that the lines `C₂ = 0` and `C₃ = 0` lie in the positive quadrant and `D ≠ 0`, no optimal
control (for `f(∞)`, the case § 12 considers, or for `f(T)` with `T ≥ b`) mixes `A`, `B` and `C`:
there is no interval `(a, b) ⊆ [0, ∞)` on which `φ₁, φ₂, φ₃ > 0` almost everywhere. -/
theorem lemma4_no_triple_mixture (P : Params) (hP : P.Positive)
    (hC₂ : P.q₁ * P.r₃ < P.q₃ * P.r₁) (hC₃ : P.q₂ * P.r₄ < P.q₃ * P.r₂) (hD : D P ≠ 0)
    (x₀ y₀ : ℝ) (hx₀ : 0 < x₀) (hy₀ : 0 < y₀) (φ : Control) (a b : ℝ) (ha : 0 ≤ a)
    (hab : a < b)
    (hφ : IsOptimalInfty P x₀ y₀ φ ∨ ∃ T : ℝ, b ≤ T ∧ IsOptimalOn P x₀ y₀ T φ) :
    ¬ (∀ᵐ t ∂(volume.restrict (Set.Ioo a b)), 0 < φ 0 t ∧ 0 < φ 1 t ∧ 0 < φ 2 t) := by sorry

end BellmanDP.ContGoldMining
