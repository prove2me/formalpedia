-- Prove2me | Theorems.Thm_ComplementarySourcing_hypothesis_at_n_two
-- name    : ComplementarySourcing.hypothesis_at_n_two
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:05:38.673995+00:00
-- url     : https://prove2.me/theorems/dab18d3f-3ea4-41a0-9c57-a8843474eb08
-- title:
--   Theorem A1's hypothesis at $n=2$, pp.A5, A11 — where $3-2\sqrt2$ comes from
-- statement:
--   Let $\epsilon_0>0$, $\sigma\ge0$ and $\sigma/\epsilon_0\le3-2\sqrt2$, and put $\epsilon_1=\epsilon_0+\sigma$, $\epsilon_2=\epsilon_0-\sigma$, $p_1=\tfrac12$. Then $\epsilon_2>0$, $\epsilon_1^2/(2\epsilon_2)\le\epsilon_2$ and $(\epsilon_0-p_1\epsilon_1)/p_1=\epsilon_2$, so that
--
--   $$2\epsilon_1+\max\Big\{\frac{\epsilon_0-p_1\epsilon_1}{p_1},\ \frac{\epsilon_1^2}{2\epsilon_2}\Big\}=3\epsilon_0+\sigma.$$
--
--   The right side is the first hypothesis of Theorem 2, and the left side is the hypothesis of Theorem A1 at $n=2$. This is the step the paper omits when it derives Theorem 2 from Theorem A1, and the constant $3-2\sqrt2=(\sqrt2-1)^2$ is exactly the condition $\epsilon_1^2\le2\epsilon_2^2$.
--
--   Differences from the source:
--   - encoding: general n, p_i → n = 2, p_1 = p_2 = ½, ϵ_1 = ϵ0 + σ, ϵ_2 = ϵ0 − σ; reason: the substitution the page prescribes on p.A11 for the proof of Theorem 2; general n is not an item of this mission
--   - reading: 0 ≤ σ ≤ ϵ0, with σ/ϵ0 and the optimal price meaningful → 0 < ε₀; reason: at ϵ0 = 0 demand is 0 at every price, so the printed unique optimum and the ratio σ/ϵ0 lose their meaning
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), Theorem A1, p.A5, and proof of Theorem 2, p.A11

import Mathlib

namespace ComplementarySourcing

/-- **Theorem A1's hypothesis at `n = 2`**, `ϵ₁ = ϵ₀ + σ`, `ϵ₂ = ϵ₀ − σ`, `p₁ = ½`: under
`σ/ϵ₀ ≤ 3 − 2√2` one has `ϵ₂ > 0`, `ϵ₁²/(2ϵ₂) ≤ ϵ₂`, `(ϵ₀ − p₁ϵ₁)/p₁ = ϵ₂`, and so
`2ϵ₁ + max{(ϵ₀ − p₁ϵ₁)/p₁, ϵ₁²/(2ϵ_n)} = 3ϵ₀ + σ`, the first hypothesis of Theorem 2.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), Theorem A1, p.A5 (PDF 33), and proof of Theorem 2, p.A11 (PDF 39).

**Formalization Note.** This is the source of the constant `3 − 2√2`: `ϵ₁² ≤ 2ϵ₂²` is
`σ/ϵ₀ ≤ (√2 − 1)²`. The page omits this computation ("We omit the details"). -/
theorem hypothesis_at_n_two {ε₀ σ : ℝ} (hε₀ : 0 < ε₀) (hσ₀ : 0 ≤ σ)
    (hσ : σ / ε₀ ≤ 3 - 2 * Real.sqrt 2) :
    0 < ε₀ - σ ∧
      (ε₀ + σ) ^ 2 / (2 * (ε₀ - σ)) ≤ ε₀ - σ ∧
      (ε₀ - 1 / 2 * (ε₀ + σ)) / (1 / 2) = ε₀ - σ ∧
      2 * (ε₀ + σ) +
          max ((ε₀ - 1 / 2 * (ε₀ + σ)) / (1 / 2)) ((ε₀ + σ) ^ 2 / (2 * (ε₀ - σ))) =
        3 * ε₀ + σ := by sorry

end ComplementarySourcing
