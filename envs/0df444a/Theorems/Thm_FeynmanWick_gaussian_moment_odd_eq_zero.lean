-- Prove2me | Theorems.Thm_FeynmanWick_gaussian_moment_odd_eq_zero
-- name    : FeynmanWick.gaussian_moment_odd_eq_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T03:40:16.507537+00:00
-- url     : https://prove2.me/theorems/b26670d1-d78f-4178-9183-548073bf9fa6
-- title:
--   Odd correlation functions of a centered Gaussian vanish
-- statement:
--   Let $\mu$ be a centered Gaussian probability measure on $\mathbb{R}^d$, so
--   $\int x_i \, d\mu = 0$ for every coordinate $i$, and let $k_1,\dots,k_{2n+1}$ be coordinate
--   labels, not necessarily distinct. Then the correlation function of odd order vanishes:
--
--   $$ \int \prod_{j=1}^{2n+1} x_{k_j}\, d\mu(x) \;=\; 0. $$
--
--   This is the first half of the source's Wick theorem: the expectation of a product of field modes
--   is zero unless the modes can be matched in pairs, which is impossible for an odd number of
--   insertions. Diagrammatically, an odd number of half-lines cannot be joined into lines.
-- source:
--   Feynman diagram, Wikipedia (revision captured 2026-09-20), https://en.wikipedia.org/wiki/Feynman_diagram, sections 'Wick theorem' and 'Higher Gaussian moments — completing Wick's theorem'

import Mathlib
import Definitions.Def_FeynmanWickPairings
open MeasureTheory ProbabilityTheory

namespace FeynmanWick

theorem gaussian_moment_odd_eq_zero {d n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsGaussian μ]
    (hcent : ∀ i : Fin d, ∫ x, x i ∂μ = 0) (k : Fin (2 * n + 1) → Fin d) :
    ∫ x, ∏ j : Fin (2 * n + 1), x (k j) ∂μ = 0 := by sorry

end FeynmanWick
