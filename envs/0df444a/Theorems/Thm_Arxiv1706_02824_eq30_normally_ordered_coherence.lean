-- Prove2me | Theorems.Thm_Arxiv1706_02824_eq30_normally_ordered_coherence
-- name    : Arxiv1706_02824.eq30_normally_ordered_coherence
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T01:45:08.273449+00:00
-- url     : https://prove2.me/theorems/dfb12d29-41bd-47c6-aaea-be5a8e904c42
-- title:
--   Eq. (30): the normally ordered fourth-order coherence factor equals 1
-- statement:
--   For a single mode with normalised mode function $u$ in the coherent state $|\alpha\rangle$, the normally ordered correlation is
--   $$\langle\alpha|E^-(x_1)E^-(x_2)E^+(x_1)E^+(x_2)|\alpha\rangle=(\hbar\omega/2)^2|\alpha|^4|u(x_1)|^2|u(x_2)|^2 .$$
--   If $\alpha\ne0$, $u(x_1)\ne0$ and $u(x_2)\ne0$, the normally ordered fourth-order coherence factor is
--   $$\gamma_\alpha^{(2,2)}(x_1,x_2)=\frac{\langle\alpha|E^-(x_1)E^-(x_2)E^+(x_1)E^+(x_2)|\alpha\rangle}{\langle\alpha|E^-(x_1)E^+(x_1)|\alpha\rangle\langle\alpha|E^-(x_2)E^+(x_2)|\alpha\rangle}=1 .$$
--   For all $x_1,x_2$, numerator minus denominator is $0$, so this definition gives an identically zero autocovariance and variance.
--
--   **Formalization Note** The nonvanishing conditions, implicit in the paper's division, are hypotheses only of the ratio.
-- source:
--   Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, On the van Cittert - Zernike theorem for intensity correlations and its applications, arXiv:1706.02824v1 (2017), claim c034; Section 6, eq. (30) and the following paragraph, PDF p. 6

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace Arxiv1706_02824

theorem eq30_normally_ordered_coherence (hbar ω : ℝ) (hhbar : 0 < hbar) (hω : 0 < ω)
    (u0 : ℝ → ℂ) (hnorm : ∫ y : ℝ, ‖u0 y‖ ^ 2 = 1) (α : ℂ) (x1 x2 : ℝ) :
    normalOrderedCorr hbar ω u0 α x1 x2 =
      (((hbar * ω / 2) ^ 2 * ‖α‖ ^ 4 * ‖u0 x1‖ ^ 2 * ‖u0 x2‖ ^ 2 : ℝ) : ℂ) ∧
    (α ≠ 0 → u0 x1 ≠ 0 → u0 x2 ≠ 0 → cohGamma22Normal hbar ω u0 α x1 x2 = 1) ∧
    normalOrderedCorr hbar ω u0 α x1 x2 -
      cohExpect α (intensityOp hbar ω u0 x1) * cohExpect α (intensityOp hbar ω u0 x2) = 0 := by sorry

end Arxiv1706_02824
