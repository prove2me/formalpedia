-- Prove2me | Theorems.Thm_DetCCHard_Supplement_theorem_6_17
-- name    : DetCCHard.Supplement.theorem_6_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:00:03.453929+00:00
-- url     : https://prove2.me/theorems/1e79a63b-9373-4800-a4ee-e2765427eab1
-- title:
--   Theorem 6.17 — the full $Q$-fold interlace restores the deletion bounds: $D(R^+) = D(W) + r$, $\mathcal P(R^+; 2^{-b}, D(W) + r)$
-- statement:
--   Let $W$ have $m \ge 1$ rows, $n \ge 1$ columns and $D(W) \ge 3$, with positive normalized rational input weights. Let $\theta > 0$ and $0 < \delta \le 1/64$. Assume that every restriction retaining row weight at least $\theta$ and column weight at least $1 - \delta$ has cost at least $D(W)$, and that $\mathcal P(W; \theta, D(W) - 1)$ holds. Let $b \ge 1$ be an integer and $Q = 2^r$ a power of two with
--   $$
--   Q\delta \ge 80b, \qquad Q\theta \le 1/20 .
--   $$
--   Then $R^+ = (I_Q(W))^{\mathsf T}$ satisfies
--   $$
--   D(R^+) = D(W) + r, \qquad \mathcal P(R^+; 2^{-b}, D(W) + r).
--   $$
--   Independently of the lower-bound hypotheses, $D(W) \le y$ implies $D(R^+) \le y + r$. The matrix $R^+$ has exactly $n^Q$ rows and $Qm$ columns.
--
--   This is the restoration step of the full-product round (with $b = L$ and $\delta = \delta_U$), returning the deletion bounds at full cost for the next round.
--
--   **Formalization Note** $R^+$ has a row for each $f \in Y^Q$ with weight $\prod_i \mu_Y(f_i)$ and a column for each $(i, u) \in [Q] \times X$ with weight $\mu_X(u)/Q$, entry $W(u, f_i)$; its deletion bounds put $2^{-b}$ on the row side.
--
--   Differences from the source:
--   - encoding: Q = 2^r a power of two, with m ≥ 1 rows and n ≥ 1 columns → Q = 2^r; m, n ≥ 1 follow from the positive normalized weights; reason: same instances
--   - encoding: R⁺ has exactly n^Q rows and Qm columns → the cardinalities of its row type Fin Q → Y and column type Fin Q × X; reason: R⁺ is defined on these types
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Theorem 6.17, p.31 (proof on p.54)

import Mathlib
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_IsWeight
import Definitions.Def_DetCCHard_DeletionBounds
import Definitions.Def_DetCCHard_interlaceOn
import Definitions.Def_DetCCHard_Supplement_RawList

namespace DetCCHard.Supplement

open DetCCHard

/-- **Theorem 6.17 (Restoring the deletion bounds)** (Gaspers–He–Mackenzie, arXiv:2508.05597, held version sha256 ad552d13…a4a03, Theorem 6.17, p.31). Let `W` have
`m ≥ 1` rows, `n ≥ 1` columns and `D(W) ≥ 3`. Let `θ > 0` and `0 < δ ≤ 1/64`. Assume that every
restriction retaining row weight at least `θ` and column weight at least `1 − δ` has cost at least
`D(W)`, and that `P(W; θ, D(W) − 1)` holds. Let `b ≥ 1` be an integer and `Q = 2^r` a power of two
with `Qδ ≥ 80b` and `Qθ ≤ 1/20`. Then `R⁺ = (I_Q(W))ᵀ` satisfies `D(R⁺) = D(W) + r` and
`P(R⁺; 2^{-b}, D(W) + r)`. Independently of the lower-bound hypotheses, `D(W) ≤ y` implies
`D(R⁺) ≤ y + r`. The matrix `R⁺` has exactly `n^Q` rows and `Qm` columns.

**Formalization Note** `W : X × Y → {0,1}` with positive normalized rational weights `μX`, `μY`
(so `m = |X| ≥ 1`, `n = |Y| ≥ 1`). `R⁺ = fullInterlaceT W Q` has a row for each `f ∈ Y^Q` with
product weight `∏ μY(f_i)` and a column for each `(i, u) ∈ [Q] × X` with weight `μX(u)/Q`; its
deletion bounds put the threshold `2^{-b}` on the row side. `θ`, `δ` are real. -/
theorem theorem_6_17 {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y] (W : X → Y → Bool)
    (μX : X → ℚ) (μY : Y → ℚ) (hμX : IsWeight μX) (hμY : IsWeight μY) (r : ℕ) :
    (∀ (θ δ : ℝ) (b : ℕ), 3 ≤ Dcost W → 0 < θ → 0 < δ → δ ≤ 1 / 64 →
      (∀ (A : Set X) (B : Set Y), θ ≤ (wt μX A : ℝ) → 1 - δ ≤ (wt μY B : ℝ) →
        Dcost W ≤ commCost W A B) →
      DeletionBounds W μX μY θ ((Dcost W : ℤ) - 1) →
      1 ≤ b → 80 * (b : ℝ) ≤ (2 : ℝ) ^ r * δ → (2 : ℝ) ^ r * θ ≤ 1 / 20 →
      Dcost (fullInterlaceT W (2 ^ r)) = Dcost W + r ∧
        DeletionBounds (fullInterlaceT W (2 ^ r)) (prodWt μY) (interlaceRowWt μX (2 ^ r))
          (1 / 2 ^ b) ((Dcost W + r : ℕ) : ℤ)) ∧
    (∀ y : ℕ, Dcost W ≤ y → Dcost (fullInterlaceT W (2 ^ r)) ≤ y + r) ∧
    Fintype.card (Fin (2 ^ r) → Y) = Fintype.card Y ^ 2 ^ r ∧
    Fintype.card (Fin (2 ^ r) × X) = 2 ^ r * Fintype.card X := by sorry

end DetCCHard.Supplement
