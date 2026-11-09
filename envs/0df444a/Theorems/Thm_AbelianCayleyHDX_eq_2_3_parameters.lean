-- Prove2me | Theorems.Thm_AbelianCayleyHDX_eq_2_3_parameters
-- name    : AbelianCayleyHDX.eq_2_3_parameters
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:34:45.332321+00:00
-- url     : https://prove2.me/theorems/7b51e4f0-1f28-4a27-9fee-ebe0cb874b0c
-- title:
--   Proof of Theorem 1.2 — Eq. (2.3): $M \le (q^2-1)(n/2h)^{6h}$, $h = O(\log(2+1/\lambda))$, $t = O_\lambda(\log n)$
-- statement:
--   Let $q = 2^h$ with $h \ge 1$.
--   1. If $n \ge 2h\,2^{t/3}$ (Eq. (2.2)), then
--   $$M = (q^2 - 1)q^{2t} \le (q^2-1)\Big(\frac{n}{2h}\Big)^{6h}. \qquad (2.3)$$
--   2. There is an absolute constant $C$ such that for every $\lambda > 0$ the least $h$ with $q = 2^h \ge 8$ and $3/(q-2) \le \lambda$ satisfies $h \le C\log(2 + 1/\lambda)$.
--   3. If $n \ge 2h\,2^{t/3}$, then $t \le 3\log_2 n$; in particular $t = O_\lambda(\log n)$.
--
--   These give the Cayley degree $n^{O(\log(2+1/\lambda))}$ and the $O_\lambda(\log n)$ triangles per edge in Theorem 1.2.
--
--   Differences from the source:
--   - reading: choosing the least admissible $q$ gives $h = O(\log(2+1/\lambda))$ → one constant $C$, chosen before $\lambda$, bounds the least admissible $h$ by $C\log(2+1/\lambda)$; reason: the $O$ has no subscript, so its constant is absolute
--   - generalization: $t = O_\lambda(\log n)$ → $t \le 3\log_2 n$ whenever $n \ge 2h\,2^{t/3}$, $h \ge 1$; reason: an explicit bound implying the $O_\lambda$ statement; it is what (2.2) gives
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), proof of Theorem 1.2, Section 2.5, p.10, Eq. (2.3)

import Mathlib

namespace AbelianCayleyHDX

/-- **Proof of Theorem 1.2: Eq. (2.3) and the parameter bounds** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), proof of Theorem 1.2,
Section 2.5, p.10, Eq. (2.3)). With `q = 2^h`:
1. if `n ≥ 2h · 2^{t/3}` (Eq. (2.2)) then `M = (q² − 1) q^{2t} ≤ (q² − 1) (n/(2h))^{6h}`;
2. choosing the least admissible `q` (the least `h` with `q = 2^h ≥ 8` and `3/(q − 2) ≤ λ`)
   gives `h = O(log(2 + 1/λ))`, with an absolute constant;
3. if `n ≥ 2h · 2^{t/3}` then `t ≤ 3 log₂ n`, so `t = O_λ(log n)`. -/
theorem eq_2_3_parameters :
    (∀ h t n : ℕ, 1 ≤ h → 2 * (h : ℝ) * (2 : ℝ) ^ ((t : ℝ) / 3) ≤ n →
      (((2 : ℝ) ^ h) ^ 2 - 1) * ((2 : ℝ) ^ h) ^ (2 * t) ≤
        (((2 : ℝ) ^ h) ^ 2 - 1) * ((n : ℝ) / (2 * h)) ^ (6 * h)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∃ h : ℕ, 8 ≤ 2 ^ h ∧ 3 / ((2 : ℝ) ^ h - 2) ≤ lam ∧
      (∀ h' < h, ¬ (8 ≤ 2 ^ h' ∧ 3 / ((2 : ℝ) ^ h' - 2) ≤ lam)) ∧
      (h : ℝ) ≤ C * Real.log (2 + 1 / lam)) ∧
    (∀ h t n : ℕ, 1 ≤ h → 2 * (h : ℝ) * (2 : ℝ) ^ ((t : ℝ) / 3) ≤ n →
      (t : ℝ) ≤ 3 * Real.logb 2 n) := by sorry

end AbelianCayleyHDX
