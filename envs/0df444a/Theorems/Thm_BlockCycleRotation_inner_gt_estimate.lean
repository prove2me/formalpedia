-- Prove2me | Theorems.Thm_BlockCycleRotation_inner_gt_estimate
-- name    : BlockCycleRotation.inner_gt_estimate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:56:39.485146+00:00
-- url     : https://prove2.me/theorems/f5106ac9-a532-4340-a6f0-5d4d164098c7
-- title:
--   The innermost estimation layer
-- statement:
--   Fix $a>0$ with $\gcd(a,a')=1$ and a cut-off $U$. The inner sum over $b' < U$ in the progression $a \mid m - a'b'$ differs from its expected value
--   $$\frac{1}{a}\sum_{1 \le b' < U} \left( \left(da + \frac{m}{a}\right) - \frac{a'}{a}\,b' \right)$$
--   by at most the size of the coefficients times $1+\log a$.
--
--   This is the analytic core of Lemmas 18 and 19 at one pair: a linear function summed over an arithmetic progression, estimated by expanding the indicator of the progression in additive characters and bounding each nontrivial character sum.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemmas 16 and 18. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L920-L935

import Mathlib

open Real Finset

theorem BlockCycleRotation.inner_gt_estimate {m d a a' : ℕ} (ha : 0 < a) (hgcd : Nat.gcd a a' = 1) (U : ℕ)
    (hU : ∀ b' ∈ Finset.Ico 1 U, a' * b' ≤ m) :
    ∃ c : ℤ,
      |((∑ b' ∈ (Finset.Ico 1 U).filter (fun b' => a ∣ (m - a' * b')),
            (d * a + (m - a' * b') / a) : ℕ) : ℝ)
          - (1 / (a : ℝ)) * ∑ b' ∈ Finset.Ico 1 U,
              ((((d * a : ℕ) : ℝ) + (m : ℝ) / a) + (-(a' : ℝ) / a) * b')|
        ≤ (|((d * a : ℕ) : ℝ) + (m : ℝ) / a| + |(-(a' : ℝ) / a)| * (U - 1 : ℕ))
            * (1 + Real.log a) := by sorry
