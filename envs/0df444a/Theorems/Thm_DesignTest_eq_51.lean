-- Prove2me | Theorems.Thm_DesignTest_eq_51
-- name    : DesignTest.eq_51
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:08:24.33335+00:00
-- url     : https://prove2.me/theorems/09b82680-fe10-49bb-a0fe-64871c001ec7
-- title:
--   Eq. (51) and the majority bound — $B\ge\frac{32}9\log\frac1{\delta}$ odd batches give error $\le e^{-9B/32}\le\delta$
-- statement:
--   Let $\delta\in(0,1/2)$ and let $B$ be an odd integer with
--   $$B\ge\frac{32}{9}\log\frac1\delta .$$
--   Let $X_1,\dots,X_B$ be independent random variables with values in $\{0,1\}$ (the error indicators of $B$ independent batches) and means $\mathbb E X_b\le1/8$. Then the majority vote errs with probability
--   $$\Pr\Big[\sum_{b=1}^{B}X_b\ge\frac B2\Big]\le\exp\Big[-2B\Big(\frac12-\frac18\Big)^2\Big]=e^{-9B/32}\le\delta .$$
--
--   This is the amplification step that turns the constant-error batch of Theorem 4.11 into a tester with failure probability $\delta_{\mathrm{fail}}$ at a cost of $O(\log(1/\delta_{\mathrm{fail}}))$ batches.
--
--   **Formalization Note** The indicators live on an arbitrary probability space and are measurable, independent in the sense of Mathlib's `iIndepFun`, and almost surely $\{0,1\}$-valued.
--
--   Differences from the source:
--   - generalization: B is the smallest odd integer with B ≥ (32/9) log(1/δ_fail) → every odd B with B ≥ (32/9) log(1/δ); reason: the smallest such B is one of them
--   - generalization: batch error indicators with values in {0, 1} → measurable random variables that are {0, 1}-valued almost surely; reason: everywhere {0,1}-valued indicators are a special case
--   - encoding: the majority error → Pr[Σ_b X_b ≥ B/2]; reason: for odd B the majority errs exactly when at least B/2 batches err
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), proof of Theorem 4.5, eq. (51), p.34, and the display following it, p.35; cited in the proof of Theorem 4.11, p.39

import Mathlib

set_option autoImplicit false

namespace DesignTest

open MeasureTheory ProbabilityTheory

/-- **Equation (51) and the majority bound** (amplification). A. Kawachi, Y. Nakata, Y. Takeuchi,
*Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), proof of Theorem 4.5,
eq. (51), p.34, and the following display, p.35; cited in the proof of Theorem 4.11, p.39.

Let `δ ∈ (0, 1/2)` and let `B` be an odd integer with `B ≥ (32/9) log(1/δ)`. If `X_1, …, X_B` are
independent `{0,1}`-valued random variables (the batch error indicators) with means at most `1/8`, the
majority errs with probability `Pr[Σ_b X_b ≥ B/2] ≤ exp(−2B(1/2 − 1/8)²) = exp(−9B/32) ≤ δ`.

**Formalization Note.** The indicators live on an arbitrary probability space; independence is Mathlib's
`iIndepFun`; `{0,1}`-valued is required almost surely. -/
theorem eq_51 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (B : ℕ) (hBodd : Odd B)
    (hB : 32 / 9 * Real.log (1 / δ) ≤ (B : ℝ)) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Fin B → Ω → ℝ) (hmeas : ∀ b, Measurable (X b))
    (hind : iIndepFun X P) (h01 : ∀ b, ∀ᵐ ω ∂P, X b ω = 0 ∨ X b ω = 1)
    (hmean : ∀ b, ∫ ω, X b ω ∂P ≤ 1 / 8) :
    P {ω | (B : ℝ) / 2 ≤ ∑ b, X b ω} ≤ ENNReal.ofReal (Real.exp (-(9 * (B : ℝ) / 32))) ∧
      Real.exp (-(9 * (B : ℝ) / 32)) ≤ δ := by sorry

end DesignTest
