-- Prove2me | Theorems.Thm_BranchTailRepair_integrated_tail
-- name    : BranchTailRepair.integrated_tail
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T15:55:27.37694+00:00
-- url     : https://prove2.me/theorems/9136d20c-f33c-446b-94b8-8e84063320b4
-- title:
--   Uniform integral bound for a logarithmically weighted rational-power tail
-- statement:
--   For $n\ge2$, real $\lambda\le1$, and $L,M\ge1$, the following integrand is integrable and satisfies
--   $$
--   \int_M^\infty (L+\log(y+3))\left(1+\frac{y^2-\lambda/4}{n}\right)^{-n}\,dy\le\frac{32L}{M^2}.
--   $$
--   The bound is uniform in $n$ and provides a polynomial tail estimate without a global Gaussian majorant.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandão Bueno. Repair of the high-tail bound in Section4.4 of On the Infinitude of Off-Critical Zeros. Elementary analysis, no novelty claim.

import Mathlib

theorem BranchTailRepair.integrated_tail (n : ℕ) (hn : 2 ≤ n) (l L M : ℝ) (hl : l ≤ 1) (hL : 1 ≤ L) (hM : 1 ≤ M) : MeasureTheory.IntegrableOn (fun y : ℝ => (L+Real.log (y+3))*((1+(y^2-l/4)/(n : ℝ))^n)⁻¹) (Set.Ioi M) ∧ (∫ y : ℝ in Set.Ioi M, (L+Real.log (y+3))*((1+(y^2-l/4)/(n : ℝ))^n)⁻¹) ≤ 32*L/M^2 := by sorry
