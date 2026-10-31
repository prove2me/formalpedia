-- Prove2me | Theorems.Thm_DirectTradeCoffee_proposition_3
-- name    : DirectTradeCoffee.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:41.677789+00:00
-- url     : https://prove2.me/theorems/542c5a31-79be-4f7a-92e9-faf593f1fbeb
-- title:
--   Proposition 3, p.15 — specialized / diversified / mixed sourcing is optimal iff (11) / (12) / neither (corrected: left derivative of $k$ at $Q_H$ in (12))
-- statement:
--   Let $k'_+$, $k'_-$ be the right and left derivatives of the cost $k$.
--
--   (a) Some optimal acreage is specialized if and only if
--
--   $$
--   \mu_\varphi + \rho\sigma_\varphi\sigma_y + \big(\bar m_c(Q_L) - \bar m_u(Q_L)\big) \le k'_+(Q_L) + c. \tag{11}
--   $$
--
--   (b) If an optimal acreage exists, then some optimal acreage is diversified if and only if
--
--   $$
--   \mu_\varphi + \rho\sigma_\varphi\sigma_y \ge k'_-(Q_H) + c. \tag{12}
--   $$
--
--   (c) Some optimal acreage is mixed if and only if neither (11) nor (12) holds.
--
--   (d) If $\sigma_y^2>0$ or $\sigma_\varphi^2>0$, any two optimal acreages lie in the same class.
--
--   So specialized sourcing is preferred when marginal revenue is low relative to marginal cost, and diversified sourcing when it is high. Both sides of each condition are marginal revenue and marginal cost at a benchmark acreage.
--
--   **Formalization Note** "Specialized", "diversified", "mixed" mean $Q\le Q_L$, $Q\ge Q_H$, $Q_L<Q<Q_H$. $k$ is not assumed differentiable, and $F$ is any law with support $\Omega$.
--
--   Differences from the source:
--   - correction: (12) uses k′(Q_H), the right derivative by the convention of p.13 → (12) uses the left derivative k′₋(Q_H), in (b) and (c); reason: with the right derivative (b) and (c) fail at a kink at Q_H; counterexample: b = 1, v = 20, v_B = 17, c = 13.25, Ω = [13, 17] × [0.5, 1.5], independent uniform laws, k(Q) = Q + 1.5 (Q − Q_H)⁺: Q* = Q_H is uniquely optimal, yet 15 ≥ 15.75 is false
--   - reading: (c) "(13) and (14) do not hold" → (11) and the corrected (12) do not hold; reason: the in-text equation references are shifted by two throughout (the proof of Proposition 3 calls (11) "(13)"); the printed (13), (14) are Corollary 1's sufficient conditions
--   - reading: "strategy S is optimal" → some optimal acreage lies in class S; reason: the universal reading is false without uncertainty: φ̃ ≡ 15, ỹ ≡ 1, c = 13.25, k(Q) = 1.75 Q makes every Q ≥ Q_D optimal; (d) recovers it under uncertainty
--   - reading: Q* is presupposed to exist (p.11) → (b) carries the hypothesis that an optimal acreage exists; (a) and (c) do not need it; reason: for k ≡ 0 and E[φ̃ỹ] > c no optimum exists although (12) holds; the conditions of (a) and (c) imply existence
--   - generalization: no such clause; "the optimal Q*" → clause (d): under uncertainty any two optimal acreages lie in the same class; reason: added so that the universal reading of "the optimal Q*" follows from (a)–(c); it specializes to the printed claim when the optimum is unique
--   - generalization: v > v_B (p.9; p.31 prints v_B > v) → no order between v and v_B is assumed; reason: no step uses it, and p.9 and p.31 disagree; every instance of the paper is covered
--   - reading: p.13 illustrates a capacity limit Q_max by k′(Q_max) = ∞ → k is real-valued and continuous on [0, ∞), as p.10 and p.31 assume; reason: the illustration lies outside the model assumption that k is a continuous function; every k of the model is covered
--   - encoding: second-stage constraint 0 ≤ q ≤ 1 → 0 ≤ q < 1; reason: at q = 1 no finite price clears the market and the objective tends to −∞; the maximum and its maximizer are unchanged
--   - encoding: F has support Ω → F(Ωᶜ) = 0 and every open ball around a point of Ω has positive mass; reason: this is the definition of the support of a measure
--   - encoding: μ_φ + ρσ_φσ_y → U.meanφ + U.cov, with the covariance ∫(φ − μ_φ)(y − 1) dF; reason: ρ is undefined when a variance is 0; the two agree whenever ρ is defined
-- source:
--   Webster–Kazaz–Gheibi, Direct Trade Sourcing Strategies for Specialty Coffee, MSOM (2024), doi:10.1287/msom.2021.0586, Proposition 3, p.15, displays (11), (12); proof p.43

import Mathlib
import Definitions.Def_DirectTradeCoffee_Model

namespace DirectTradeCoffee

/-- **Proposition 3** (corrected), Webster–Kazaz–Gheibi, *Direct Trade Sourcing Strategies for
Specialty Coffee*, MSOM (2024), doi:10.1287/msom.2021.0586, p.15: the optimal sourcing strategy.

* (a) Some optimal acreage is specialized iff (11):
  `μ_φ + ρσ_φσ_y + (m̄_c(Q_L) − m̄_u(Q_L)) ≤ k′₊(Q_L) + c`.
* (b) If an optimal acreage exists, some optimal acreage is diversified iff (12), with the left
  derivative: `μ_φ + ρσ_φσ_y ≥ k′₋(Q_H) + c`.
* (c) Some optimal acreage is mixed iff neither (11) nor (12) holds.
* (d) Under uncertainty (`σ_y² > 0` or `σ_φ² > 0`), any two optimal acreages lie in the same class.

**Formalization Note.** "Strategy S is optimal" is read "some optimal acreage lies in S"; (d) gives
the reading "every optimal acreage lies in S" under uncertainty. That reading fails without
uncertainty: for `φ̃ ≡ φ`, `ỹ ≡ 1` and `k(Q) = (φ − c) Q`, every `Q ≥ Q_D` is optimal. (b) is
the only part with an existence hypothesis: for `k ≡ 0` with `E[φ̃ỹ] > c` there is no optimum and
(12) holds. The printed (12) uses the right derivative, by the convention of p.13; that is false
when `k` kinks at `Q_H`. (c)'s printed "(13) and (14)" are (11) and (12): the paper's in-text
equation references are shifted by two. -/
theorem proposition_3 (P : Params) {k : ℝ → ℝ} (hk : IsCost k) (U : Uncertainty) :
    ((∃ Q, IsOptimalAcreage P k U Q ∧ IsSpecialized P U Q) ↔
      U.meanφ + U.cov + (mcBar P U (QL P U) - muBar P U (QL P U)) ≤ kRight k (QL P U) + P.c) ∧
    ((∃ Q, IsOptimalAcreage P k U Q) →
      ((∃ Q, IsOptimalAcreage P k U Q ∧ IsDiversified P U Q) ↔
        kLeft k (QH P U) + P.c ≤ U.meanφ + U.cov)) ∧
    ((∃ Q, IsOptimalAcreage P k U Q ∧ IsMixed P U Q) ↔
      ¬ (U.meanφ + U.cov + (mcBar P U (QL P U) - muBar P U (QL P U)) ≤ kRight k (QL P U) + P.c) ∧
      ¬ (kLeft k (QH P U) + P.c ≤ U.meanφ + U.cov)) ∧
    ((0 < U.varY ∨ 0 < U.varφ) →
      ∀ Q₁ Q₂, IsOptimalAcreage P k U Q₁ → IsOptimalAcreage P k U Q₂ →
        (IsSpecialized P U Q₁ ↔ IsSpecialized P U Q₂) ∧
        (IsMixed P U Q₁ ↔ IsMixed P U Q₂) ∧
        (IsDiversified P U Q₁ ↔ IsDiversified P U Q₂)) := by sorry

end DirectTradeCoffee
