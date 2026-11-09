-- Prove2me | Theorems.Thm_AbelianCayleyHDX_binomial_bounds
-- name    : AbelianCayleyHDX.binomial_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:34:25.531428+00:00
-- url     : https://prove2.me/theorems/22bd13b6-17db-4b6c-ac42-cf13fdbf1fdf
-- title:
--   Proof of Lemma 3.2 (Section 4.3) — $\binom{3k}{k} \ge (27/4)^k/(3k+1) \ge 2^{t/3}$
-- statement:
--   For every integer $k \ge 0$,
--   $$\binom{3k}{k} \ge \frac{(27/4)^k}{3k+1},$$
--   and with $t = 2g + 1$ and $k = \lfloor g/4 \rfloor$,
--   $$\frac{(27/4)^k}{3k+1} \ge 2^{t/3} \qquad \text{for all sufficiently large } g.$$
--   These are the last two inequalities of the chain $\dim_F A(D) \ge \binom{3k}{k} \ge (27/4)^k/(3k+1) \ge 2^{t/3}$ in the proof of Lemma 3.2 (the first one is Proposition 4.6).
--
--   Differences from the source: none.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), proof of Lemma 3.2, Section 4.3, p.18

import Mathlib

namespace AbelianCayleyHDX

/-- **Proof of Lemma 3.2 (Section 4.3): the binomial bounds** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), proof of Lemma 3.2,
Section 4.3, p.18). For every `k ≥ 0`, `\binom{3k}{k} ≥ (27/4)^k / (3k + 1)`; and with
`t = 2g + 1` and `k = ⌊g/4⌋`, `(27/4)^k / (3k + 1) ≥ 2^{t/3}` for all sufficiently large `g`. -/
theorem binomial_bounds :
    (∀ k : ℕ, (27 / 4 : ℝ) ^ k / (3 * (k : ℝ) + 1) ≤ ((Nat.choose (3 * k) k : ℕ) : ℝ)) ∧
    ∃ g₀ : ℕ, ∀ g : ℕ, g₀ ≤ g →
      (2 : ℝ) ^ (((2 * g + 1 : ℕ) : ℝ) / 3) ≤ (27 / 4 : ℝ) ^ (g / 4) / (3 * ((g / 4 : ℕ) : ℝ) + 1) := by sorry

end AbelianCayleyHDX
