-- Prove2me | Theorems.Thm_FeynmanWick_wick_four_point
-- name    : FeynmanWick.wick_four_point
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T03:42:34.934673+00:00
-- url     : https://prove2.me/theorems/c07cdaf7-b979-4c4a-bf83-91df41199416
-- title:
--   Four-point function: $\langle x_1x_2x_3x_4\rangle = G_{12}G_{34}+G_{13}G_{24}+G_{14}G_{23}$
-- statement:
--   Let $\mu$ be a centered Gaussian probability measure on $\mathbb{R}^d$ and let
--   $k_1, k_2, k_3, k_4$ be coordinate labels, not necessarily distinct. Writing
--   $G_{ab} = \int x_{k_a} x_{k_b} \, d\mu$ for the two-point function, the four-point correlation
--   function is the sum over the three pairings of four objects:
--
--   $$ \langle x_{k_1} x_{k_2} x_{k_3} x_{k_4} \rangle \;=\; G_{12}G_{34} \,+\, G_{13}G_{24} \,+\, G_{14}G_{23}. $$
--
--   This is the worked example displayed in the source, where the three terms correspond to the three
--   Feynman diagrams that join four half-lines into two lines. It is the first instance of the general
--   theorem in which the combinatorics is visible, and a natural stepping stone: the general statement
--   must reproduce it verbatim for $n = 2$.
-- source:
--   Feynman diagram, Wikipedia (revision captured 2026-09-20), https://en.wikipedia.org/wiki/Feynman_diagram, sections 'Wick theorem' and 'Higher Gaussian moments — completing Wick's theorem'

import Mathlib
import Definitions.Def_FeynmanWickPairings
open MeasureTheory ProbabilityTheory

namespace FeynmanWick

theorem wick_four_point {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsGaussian μ]
    (hcent : ∀ i : Fin d, ∫ x, x i ∂μ = 0) (k : Fin 4 → Fin d) :
    ∫ x, x (k 0) * x (k 1) * x (k 2) * x (k 3) ∂μ
      = (∫ x, x (k 0) * x (k 1) ∂μ) * (∫ x, x (k 2) * x (k 3) ∂μ)
        + (∫ x, x (k 0) * x (k 2) ∂μ) * (∫ x, x (k 1) * x (k 3) ∂μ)
        + (∫ x, x (k 0) * x (k 3) ∂μ) * (∫ x, x (k 1) * x (k 2) ∂μ) := by sorry

end FeynmanWick
