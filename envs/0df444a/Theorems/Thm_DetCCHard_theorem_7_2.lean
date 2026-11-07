-- Prove2me | Theorems.Thm_DetCCHard_theorem_7_2
-- name    : DetCCHard.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:29.991454+00:00
-- url     : https://prove2.me/theorems/1ae56e21-ce39-49e0-adf5-485e10a95cbf
-- title:
--   Theorem 7.2 — a final interlace on an 8192-wise independent list restores the deletion bounds at full cost $C + \log Q$
-- statement:
--   Let $0 < \varphi \le 1$, $0 < \delta \le 1/64$ and $\theta > 0$. Suppose $W$, with input weights $\mu_X, \mu_Y$, satisfies $D(W) = C \ge 3$, $\mathcal P(W; \theta, C-1)$, and $D(W[A, B]) \ge C$ whenever $\mu_X(A) \ge \theta$ and $\mu_Y(B) \ge 1 - \delta$. Let $Q$ be a power of two with
--   $$
--   Q \ge 128\bigl(e(\varphi, \delta/2) + 1\bigr), \qquad Q\theta \le 1/20 .
--   $$
--   Form the $Q$-fold interlace of $W$ on any exactly 8192-wise independent tuple list with marginal $\mu_Y$ and transpose it to obtain $R^+$. Then
--   $$
--   D(R^+) = C + \log Q, \qquad \mathcal P(R^+; \varphi, C + \log Q).
--   $$
--   Independently of the lower-bound hypotheses, a protocol of depth $U$ for $W$ yields one of depth $U + \log Q$ for $R^+$.
--
--   This is the last step of each explicit round: it returns the deletion bounds the next round needs.
--
--   **Formalization Note** $Q = 2^r$. $R^+$ has a row for each label (weights $\nu$) and a column $(i, u) \in [Q] \times X$ (weights $\mu_X(u)/Q$), with entry $W(u, z_i(\ell))$; its deletion bounds put $\varphi$ on the label side. The second claim is stated for every $W$ and every tuple list, as a protocol for $W$ correct on all inputs yielding a protocol for $R^+$ correct on all inputs.
--
--   Differences from the source:
--   - encoding: Q a power of two, log Q → Q = 2^r; reason: same instances
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Theorem 7.2, p.33

import Mathlib
import Definitions.Def_DetCCHard_Protocol
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_IsWeight
import Definitions.Def_DetCCHard_DeletionBounds
import Definitions.Def_DetCCHard_TupleList
import Definitions.Def_DetCCHard_interlaceOn
import Definitions.Def_DetCCHard_epsVT

namespace DetCCHard

/-- **Theorem 7.2 (restoring the deletion bounds)** (Gaspers–He–Mackenzie, arXiv:2508.05597, held
version sha256 ad552d13…a4a03, Theorem 7.2, p.33). Let `0 < φ ≤ 1`, `0 < δ ≤ 1/64` and `θ > 0`.
Suppose `W`, with input weights `μX`, `μY`, satisfies `D(W) = C ≥ 3`, `P(W; θ, C − 1)`, and
`D(W[A, B]) ≥ C` whenever `μX(A) ≥ θ` and `μY(B) ≥ 1 − δ`. Let `Q` be a power of two with
`Q ≥ 128 (e(φ, δ/2) + 1)` and `Qθ ≤ 1/20`. Form the `Q`-fold interlace of `W` on any exactly
8192-wise independent tuple list with marginal `μY`, and transpose it to obtain `R⁺`. Then
`D(R⁺) = C + log Q` and `P(R⁺; φ, C + log Q)`. Independently of the lower-bound hypotheses, a
protocol of depth `U` for `W` yields one of depth `U + log Q` for `R⁺`.

**Formalization Note** `Q = 2^r`, so `log Q = r`. `R⁺` has a row for each list label `ℓ` (weights
`ν`) and a column for each `(i, u) ∈ [Q] × X` (weights `μX(u)/Q`), with entry `W(u, z_i(ℓ))`; its
deletion bounds put the threshold `φ` on the label side. The second conjunct holds for every
tuple list and every `W`, with no hypothesis beyond the protocol for `W`. `φ`, `δ`, `θ` are
real. -/
theorem theorem_7_2 {X Y : Type} [Fintype X] [Fintype Y] (W : X → Y → Bool) (μX : X → ℚ)
    (μY : Y → ℚ) (hμX : IsWeight μX) (hμY : IsWeight μY) (r : ℕ)
    (T : TupleList Y (Fin (2 ^ r))) :
    (∀ (φ δ θ : ℝ) (C : ℕ), 0 < φ → φ ≤ 1 → 0 < δ → δ ≤ 1 / 64 → 0 < θ →
      Dcost W = C → 3 ≤ C → DeletionBounds W μX μY θ ((C : ℤ) - 1) →
      (∀ (A : Set X) (B : Set Y), θ ≤ (wt μX A : ℝ) → 1 - δ ≤ (wt μY B : ℝ) →
        C ≤ commCost W A B) →
      128 * (eVT φ (δ / 2) + 1) ≤ 2 ^ r → (2 ^ r : ℝ) * θ ≤ 1 / 20 →
      ExactlyIndep T 8192 μY →
      Dcost (fun ℓ p => interlaceOn W T p ℓ) = C + r ∧
        DeletionBounds (fun ℓ p => interlaceOn W T p ℓ) T.ν (interlaceRowWt μX (2 ^ r)) φ
          ((C : ℤ) + r)) ∧
    ∀ P : Protocol X Y, (∀ x y, P.eval x y = W x y) →
      ∃ P' : Protocol T.L (Fin (2 ^ r) × X), P'.depth ≤ P.depth + r ∧
        ∀ ℓ p, P'.eval ℓ p = interlaceOn W T p ℓ := by sorry

end DetCCHard
