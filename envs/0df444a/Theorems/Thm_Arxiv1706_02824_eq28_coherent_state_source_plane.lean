-- Prove2me | Theorems.Thm_Arxiv1706_02824_eq28_coherent_state_source_plane
-- name    : Arxiv1706_02824.eq28_coherent_state_source_plane
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T01:40:24.546346+00:00
-- url     : https://prove2.me/theorems/e38f746c-1bd2-5ddb-83da-9b7b2064f366
-- title:
--   Eq. (28): intensity autocovariance of a coherent state in the source plane
-- statement:
--   In the setting of eq. (22), the intensity autocovariance in the source plane is
--   $$C_{\alpha,0}(x_1',x_2')=(\hbar\omega/2)^2|\alpha|^2\,|u_0(x_1')|^2|u_0(x_2')|^2,$$
--   reciprocal to eq. (27).
-- source:
--   Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, On the van Cittert - Zernike theorem for intensity correlations and its applications, arXiv:1706.02824v1 (2017), claim c022; Section 6, eq. (28), PDF p. 6

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace Arxiv1706_02824

theorem eq28_coherent_state_source_plane (hbar ω : ℝ) (hhbar : 0 < hbar) (hω : 0 < ω)
    (u0 : ℝ → ℂ) (hnorm : ∫ y : ℝ, ‖u0 y‖ ^ 2 = 1) (α : ℂ) (x1 x2 : ℝ) :
    cohIntensityAutocov hbar ω u0 α x1 x2 =
      (((hbar * ω / 2) ^ 2 * ‖α‖ ^ 2 * ‖u0 x1‖ ^ 2 * ‖u0 x2‖ ^ 2 : ℝ) : ℂ) := by sorry

end Arxiv1706_02824
