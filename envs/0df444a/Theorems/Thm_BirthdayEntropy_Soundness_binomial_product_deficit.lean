-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_binomial_product_deficit
-- name    : BirthdayEntropy.Soundness.binomial_product_deficit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T01:00:27.645212+00:00
-- url     : https://prove2.me/theorems/8ae73346-97a5-497a-b48a-77219b666c9e
-- title:
--   Binomial product bound with a support deficit
-- statement:
--   Let $a,b,n,\ell$ be nonnegative integers with $\ell\le a,b,n$, and let $t\ge0$ be real. If $a+b+t\le2n$, then
--
--   $$\binom a\ell\binom b\ell\le\binom n\ell^2\exp(-\ell t/n).$$
--
--   This integer-exact product estimate controls the two unrestricted signed-subset counts for a fixed flattening. Taking $t=0$ gives their common baseline, while a positive support deficit gives an exponential penalty. The case $n=0$ forces $\ell=0$ and remains valid under the usual total real-division convention.
-- source:
--   Popa, Entropy-Weighted Soundness for Multi-Answer Birthday Graphs, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, proof of Lemma 4.5, equations (7) and (8), PDF p10 / printed p9. The binomial-product calculation is stated separately with arbitrary integer support sizes and a real nonnegative deficit.

import Mathlib
noncomputable section
open scoped Classical

theorem BirthdayEntropy.Soundness.binomial_product_deficit (a b n ℓ : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (ha : ℓ ≤ a) (hb : ℓ ≤ b) (hn : ℓ ≤ n) (hs : (a : ℝ)+b+t ≤ 2*n) :
    (Nat.choose a ℓ : ℝ) * (Nat.choose b ℓ : ℝ) ≤ (Nat.choose n ℓ : ℝ)^2 *
      Real.exp (-(ℓ : ℝ)*t/n) := by sorry
