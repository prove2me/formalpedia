-- Prove2me | Theorems.Thm_BlottoFPTAS_Main_rounding_bound
-- name    : BlottoFPTAS.Main.rounding_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:39:59.147196+00:00
-- url     : https://prove2.me/theorems/e922e50b-7249-48dc-b4b5-dbe86f2901e1
-- title:
--   §5.1, value rounding bound — rounding α_j to ⌈Mα_j⌉/A moves the vector by less than 2r/M in ℓ1
-- statement:
--   For positive numbers $\alpha_1,\dots,\alpha_r$ summing to one and a scale $M>0$, let $a_j=\lceil M\alpha_j\rceil$ and $A=\sum_ja_j$, and replace each $\alpha_j$ by $a_j/A$. The new numbers are positive and sum to one, $M\le A<M+r$, and
--   $$\sum_j\Big|\frac{a_j}A-\alpha_j\Big|\le\sum_j\Big|\frac{a_j}A-\frac{M\alpha_j}A\Big|+\sum_j\Big|\frac{M\alpha_j}A-\alpha_j\Big|=\frac{2(A-M)}A<\frac{2r}M.$$
--   Both value roundings of §5.1 (scales $256n/e$ and $512m/e$) use this bound.
--
--   Differences from the source:
--   - encoding: the new numbers have the common denominator A → not a separate clause: a_j are natural numbers and A their sum, so a_j/A has denominator A by construction; reason: a definitional fact, not a mathematical claim
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 30, §5.1, value rounding bound

import Mathlib

namespace BlottoFPTAS.Main

/-- **§5.1, value rounding bound** (Bichler, Ghosh, arXiv:2611.05221, held version sha256
cac3638e…, p. 30). For positive numbers `α_1, …, α_r` summing to one and a scale `M > 0`, let
`a_j = ⌈M α_j⌉` and `A = ∑_j a_j`. Then the numbers `a_j / A` are positive and sum to one,
`M ≤ A < M + r`, and
`∑_j |a_j/A − α_j| ≤ ∑_j |a_j/A − Mα_j/A| + ∑_j |Mα_j/A − α_j| = 2(A − M)/A < 2r/M`. -/
theorem rounding_bound {r : ℕ} (α : Fin r → ℝ) (hα : ∀ j, 0 < α j) (hsum : ∑ j, α j = 1)
    (M : ℝ) (hM : 0 < M) :
    let a : Fin r → ℕ := fun j => ⌈M * α j⌉₊
    let A : ℝ := ∑ j, (a j : ℝ)
    (∀ j, 0 < (a j : ℝ) / A) ∧ ∑ j, (a j : ℝ) / A = 1 ∧
      M ≤ A ∧ A < M + r ∧
      ∑ j, |(a j : ℝ) / A - α j| ≤
        ∑ j, |(a j : ℝ) / A - M * α j / A| + ∑ j, |M * α j / A - α j| ∧
      ∑ j, |(a j : ℝ) / A - M * α j / A| + ∑ j, |M * α j / A - α j| = 2 * (A - M) / A ∧
      2 * (A - M) / A < 2 * r / M := by sorry

end BlottoFPTAS.Main
