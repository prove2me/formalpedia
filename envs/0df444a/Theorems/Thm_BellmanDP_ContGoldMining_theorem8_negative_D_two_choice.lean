-- Prove2me | Theorems.Thm_BellmanDP_ContGoldMining_theorem8_negative_D_two_choice
-- name    : BellmanDP.ContGoldMining.theorem8_negative_D_two_choice
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T17:43:48.587881+00:00
-- url     : https://prove2.me/theorems/06fc6653-e1d2-4166-92bb-b9ef57278095
-- title:
--   Chapter VIII, "Theorem 8" — if $D < 0$ the optimal policy never uses $C$ and has the two-choice form
-- statement:
--   Consider the three-choice continuous gold-mining process of § 12: decisions $A$, $B$, $C$ with positive failure rates $q_1, q_2, q_3$ and positive mining rates $r_1, r_2, r_3, r_4$, where $C$ mines A at relative rate $r_3$ and B at relative rate $r_4$. Let $x_0, y_0 > 0$, assume the standing assumption $r_3 > r_4$ of § 15, and suppose
--   $$D = q_1 r_2 r_3 + q_2 r_1 r_4 - q_3 r_1 r_2 < 0.$$
--   Then the problem of maximizing $f(\infty)$ never uses a $C$-policy and has the two-choice form:
--
--   1. there is a two-choice control ($\varphi_3 = 0$) following the rule of Theorem 1 — $A$ below the line $C_1 = q_1 r_2 y - q_2 r_1 x = 0$, $B$ above it, and the mixture $\varphi_1 = r_2/(r_1 + r_2)$, $\varphi_2 = r_1/(r_1 + r_2)$ on it;
--   2. every such control maximizes $f(\infty)$ among all admissible three-choice controls;
--   3. every admissible three-choice control that maximizes $f(\infty)$ has $\varphi_3(t) = 0$ for almost every $t \ge 0$.
--
--   This is the case, complementary to Theorem 2 ($D > 0$), in which the third decision is useless and the chapter's two-choice solution applies unchanged (Fig. 8).
--
--   **Formalization Note** The theorem is printed as "Theorem 8"; it is the third theorem of Chapter VIII. $D < 0$ implies that the lines $C_2 = 0$ and $C_3 = 0$ lie in the positive quadrant, so the book's assumption of §§ 13–15 on those lines needs no separate hypothesis. The open quadrant $x_0, y_0 > 0$ is the region the book analyses; at $x_0 = y_0 = 0$ every control is optimal and part 3 fails. "Never uses a $C$-policy" is read as $\varphi_3 = 0$ almost everywhere, which also excludes the mixtures $AC$ and $BC$, as Fig. 8 shows.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter VIII, § 16, Theorem 8 (the third theorem of Chapter VIII), p. 241, Fig. 8; standing assumption r3 > r4 of § 15, p. 236

import Mathlib
import Definitions.Def_BellmanDP_ContGoldMining_Process
import Definitions.Def_BellmanDP_ContGoldMining_Switching

namespace BellmanDP.ContGoldMining

open MeasureTheory

/-- Bellman, *Dynamic Programming*, Ch. VIII, § 16, "Theorem 8" (the chapter's third theorem),
p. 241: under the standing assumption `r₃ > r₄` of § 15, if
`D = q₁ r₂ r₃ + q₂ r₁ r₄ − q₃ r₁ r₂ < 0`, the problem of maximizing `f(∞)` never uses a
`C`-policy and has the two-choice form of Theorem 1: a two-choice control following the rule of
Theorem 1 exists and is optimal among all three-choice controls, and every optimal three-choice
control has `φ₃ = 0` almost everywhere. -/
theorem theorem8_negative_D_two_choice (P : Params) (hP : P.Positive) (hr : P.r₄ < P.r₃)
    (hD : D P < 0) (x₀ y₀ : ℝ) (hx₀ : 0 < x₀) (hy₀ : 0 < y₀) :
    (∃ φ₁ : ℝ → ℝ, TwoAdmissible φ₁ ∧ FollowsIndexRule P.q₁ P.q₂ P.r₁ P.r₂ x₀ y₀ φ₁) ∧
    (∀ φ₁ : ℝ → ℝ, TwoAdmissible φ₁ → FollowsIndexRule P.q₁ P.q₂ P.r₁ P.r₂ x₀ y₀ φ₁ →
      IsOptimalInfty P x₀ y₀ (twoChoice φ₁)) ∧
    ∀ φ : Control, IsOptimalInfty P x₀ y₀ φ →
      ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))), φ 2 t = 0 := by sorry

end BellmanDP.ContGoldMining
