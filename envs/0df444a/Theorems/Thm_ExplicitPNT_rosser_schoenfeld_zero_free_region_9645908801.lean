-- Prove2me | Theorems.Thm_ExplicitPNT_rosser_schoenfeld_zero_free_region_9645908801
-- name    : ExplicitPNT.rosser_schoenfeld_zero_free_region_9645908801
-- status  : Open
-- author  : @abcdefg
-- created : 2026-10-09T15:13:31.452995+00:00
-- url     : https://prove2.me/theorems/8c452b66-6bf1-4f95-8a1b-a4ebef851450
-- title:
--   Rosser–Schoenfeld starting zero-free region with R = 9.645908801
-- statement:
--   Let $s=\sigma+it$ with $t\ge2$. Then
--   $$
--   \sigma\ge1-\frac{1}{9.645908801\log t}
--   \quad\Longrightarrow\quad \zeta(s)\ne0.
--   $$
--   This is the positive-height form of the classical starting region used in Kadiri's iteration.
-- source:
--   J. B. Rosser and L. Schoenfeld, Sharper bounds for the Chebyshev functions θ(x) and ψ(x), Math. Comp. 29 (1975), 243–269. Exact region and starting constant restated in H. Kadiri, Une région explicite sans zéros pour la fonction ζ de Riemann, author's preprint pp.2 and 5, §1 and §2: https://www.cs.uleth.ca/~kadiri/articles/zeta-acta-04-09-07.pdf

import Mathlib.NumberTheory.LSeries.RiemannZeta

theorem ExplicitPNT.rosser_schoenfeld_zero_free_region_9645908801 (s : ℂ)
    (ht : 2 ≤ s.im)
    (hσ : 1 - 1 / ((9645908801 / 1000000000 : ℝ) * Real.log s.im) ≤ s.re) :
    riemannZeta s ≠ 0 := by sorry
