-- Prove2me | Theorems.Thm_ExplicitPNT_kadiri_zero_free_region_569693
-- name    : ExplicitPNT.kadiri_zero_free_region_569693
-- status  : Open
-- author  : @abcdefg
-- created : 2026-10-09T14:30:17.501648+00:00
-- url     : https://prove2.me/theorems/c1dc19b4-cc34-4987-a509-85f0593704cc
-- title:
--   Kadiri's explicit zero-free region with R₀ = 5.69693
-- statement:
--   Let $s=\sigma+it$ be a complex number. If $|t|\ge2$ and
--   $$\sigma\ge1-\frac{1}{5.69693\log|t|},$$
--   then
--   $$\zeta(s)\ne0.$$
--
--   This is Kadiri's explicit classical zero-free region. It supplies a concrete admissible constant for quantitative estimates for the Chebyshev functions. The height condition excludes the pole at $s=1$.
-- source:
--   H. Kadiri, Une région explicite sans zéros pour la fonction ζ de Riemann, Acta Arith. 117 (2005), 303–339, Théorème 1.1. Author's preprint p.2: https://www.cs.uleth.ca/~kadiri/articles/zeta-acta-04-09-07.pdf ; DOI 10.4064/aa117-4-1.

import Mathlib.NumberTheory.LSeries.RiemannZeta

theorem ExplicitPNT.kadiri_zero_free_region_569693 (s : ℂ)
    (ht : 2 ≤ |s.im|)
    (hσ : 1 - 1 / ((569693 / 100000 : ℝ) * Real.log |s.im|) ≤ s.re) :
    riemannZeta s ≠ 0 := by sorry
