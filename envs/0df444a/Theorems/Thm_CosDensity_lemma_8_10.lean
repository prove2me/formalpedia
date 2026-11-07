-- Prove2me | Theorems.Thm_CosDensity_lemma_8_10
-- name    : CosDensity.lemma_8_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:37:48.857889+00:00
-- url     : https://prove2.me/theorems/23c03450-8bb6-4f71-8bbb-423dc7e9adc4
-- title:
--   Lemma 8.10 — nearby exact rational unit vectors with few bits
-- statement:
--   Let $\phi\ge2$, let $x\in\mathbb R^\phi$ with $\|x\|=1$ and last coordinate $x_\phi>0$, and let $\eta\in(0,1)$. There is $\hat x\in\mathbb Q^\phi$ with
--
--   $$\|\hat x\|=1,\qquad \hat x_\phi>0,\qquad \|\hat x-x\|\le\eta,$$
--
--   and the numerator and denominator of every coordinate of $\hat x$ have $O(\log\phi+\log(1/\eta)+\log(1/x_\phi))$ bits, with an absolute constant in the $O(\cdot)$.
--
--   This makes the hard instance exactly representable with $O_p(\log d)$-bit rational coordinates.
--
--   Differences from the source:
--   - encoding: ϕ ≥ 2, x = (x′, x_ϕ); O(log ϕ + log 1/η + log 1/x_ϕ) bits for numerator and denominator → ϕ = n + 1 with n ≥ 1, x_ϕ = x (Fin.last n); an absolute C > 0 with |num|, den ≤ 2^{C·L}, L = log₂ϕ + log₂(1/η) + log₂(1/x_ϕ), for the reduced fraction; reason: a b-bit integer is at most 2^b; L ≥ 1 on this domain, so a constant multiple is the O(·); the reduced fraction has the smallest numerator and denominator
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.8, Lemma 8.10, p.36 (pdf_page 37)

import Mathlib

namespace CosDensity

/-- **Lemma 8.10** (exact rational unit vectors). Q. Zhang, *Frequency Moments Beyond Equality:
Streaming Cosine Density Moments*, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.8,
Lemma 8.10, p.36 (pdf_page 37).

Let `ϕ ≥ 2`, let `x ∈ ℝ^ϕ` with `‖x‖ = 1` and last coordinate `x_ϕ > 0`, and let `η ∈ (0, 1)`.
There is `x̂ ∈ ℚ^ϕ` with `‖x̂‖ = 1`, `x̂_ϕ > 0` and `‖x̂ − x‖ ≤ η`, and the numerator and the
denominator of every coordinate of `x̂` have `O(log ϕ + log 1/η + log 1/x_ϕ)` bits.

**Formalization Note.** `ϕ = n + 1` with `n ≥ 1`; the last coordinate is `Fin.last n`. The
`O(·)` constant `C` is absolute (chosen before `ϕ`, `x`, `η`), and "`b` bits" is `≤ 2^b` for the
reduced numerator (in absolute value) and denominator. `‖x̂‖ = 1` is `Σ_k x̂_k² = 1` in `ℝ`. The
logarithm `L = log₂ ϕ + log₂(1/η) + log₂(1/x_ϕ)` is at least `1` on this domain. -/
theorem lemma_8_10 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ x : EuclideanSpace ℝ (Fin (n + 1)), ‖x‖ = 1 →
      0 < x (Fin.last n) → ∀ η : ℝ, 0 < η → η < 1 →
        ∃ xh : Fin (n + 1) → ℚ, ∑ k, ((xh k : ℝ)) ^ 2 = 1 ∧ 0 < xh (Fin.last n) ∧
          ‖(WithLp.toLp 2 (fun k => (xh k : ℝ)) : EuclideanSpace ℝ (Fin (n + 1))) - x‖ ≤ η ∧
          ∀ k, ((xh k).num.natAbs : ℝ) ≤
                (2 : ℝ) ^ (C * (Real.logb 2 ((n : ℝ) + 1) + Real.logb 2 (1 / η) +
                  Real.logb 2 (1 / x (Fin.last n)))) ∧
              ((xh k).den : ℝ) ≤
                (2 : ℝ) ^ (C * (Real.logb 2 ((n : ℝ) + 1) + Real.logb 2 (1 / η) +
                  Real.logb 2 (1 / x (Fin.last n)))) := by sorry

end CosDensity
