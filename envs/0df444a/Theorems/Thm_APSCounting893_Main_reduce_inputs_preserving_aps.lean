-- Prove2me | Theorems.Thm_APSCounting893_Main_reduce_inputs_preserving_aps
-- name    : APSCounting893.Main.reduce_inputs_preserving_aps
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:24:25.753594+00:00
-- url     : https://prove2.me/theorems/a3df8e6e-5c5a-4517-abaf-d628a3eed042
-- title:
--   Proposition 3.14 — Reduce inputs while preserving APS
-- statement:
--   Let $F=(f_1,\ldots,f_m):\mathbb C^n\to\mathbb C^m$ have nonconstant coordinates, image dimension $1\le r<m$, and $d=\max(1,\deg f_i)$. Let $B\subset\mathbb Q$ be finite and nonempty. Sample all coefficients of $n-r$ affine equations independently from $B$, parametrize the resulting plane, and, if $m>r+1$, sample $r+1$ linear combinations of the outputs. Then
--
--   $$\Pr[\dim\overline{\widetilde F(\mathbb C^r)}=r\ \text{and}\ (\operatorname{APS}(F)\iff\operatorname{APS}(\widetilde F))]\ge1-\frac{2(n-r)d^m+(r+1)d^r}{|B|}.$$
--
--   An unsuccessful parametrization is part of the failure event. The output is the actual composed and projected map $\mathbb C^r\to\mathbb C^{r+1}$, with both directions of APS preservation retained.
--
--   Differences from the source:
--   - encoding: random affine sections and optional output projection → cardinality ratio on a finite product sample space, using a selected rational affine parametrization; reason: all coefficients are independent and uniform, and unused output coefficients when m=r+1 do not change the probability
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Proposition 3.14, p. 14, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_RandomReduction

set_option autoImplicit false

namespace APSCounting893.Main

theorem reduce_inputs_preserving_aps (n m r : ℕ) (F : PolynomialMap ℂ n m)
    (hnonconstant : ∀ i, 0 < (F i).totalDegree)
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞))
    (hr : 1 ≤ r) (hrm : r < m) (B : Finset ℚ) (hB : B.Nonempty) :
    reductionSuccessProbability (r := r) F B ≥
      1 - ((2 * (n - r) * inputDegree F ^ m + (r + 1) * inputDegree F ^ r : ℕ) : ℝ) /
        (B.card : ℝ) := by sorry

end APSCounting893.Main
