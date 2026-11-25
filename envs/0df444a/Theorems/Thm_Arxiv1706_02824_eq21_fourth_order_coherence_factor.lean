-- Prove2me | Theorems.Thm_Arxiv1706_02824_eq21_fourth_order_coherence_factor
-- name    : Arxiv1706_02824.eq21_fourth_order_coherence_factor
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T01:17:44.41696+00:00
-- url     : https://prove2.me/theorems/42cdc3eb-0dfc-47a8-b922-f6f9ad8ecfa3
-- title:
--   Eq. (21): fourth-order coherence factor $\gamma^{(2,2)}=1+c^{(2,2)}$
-- statement:
--   Let the quasi-monochromatic amplitudes $V(x)$ have circular Gaussian statistics, and let $\langle I(x_1)\rangle,\langle I(x_2)\rangle>0$. Then
--   $$\gamma^{(2,2)}(x_1,x_2)=\frac{\langle I(x_1)I(x_2)\rangle}{\langle I(x_1)\rangle\langle I(x_2)\rangle}=\frac{\langle I(x_1)\rangle\langle I(x_2)\rangle+|J(x_1,x_2)|^2}{\langle I(x_1)\rangle\langle I(x_2)\rangle}=1+c^{(2,2)}(x_1,x_2).$$
--   Consequently:
--
--   1. $1\le\gamma^{(2,2)}\le2$.
--   2. $\gamma^{(2,2)}=2$ (the maximum) if and only if $|\gamma^{(1,1)}|=1$, i.e. complete second-order coherence.
--   3. $\gamma^{(2,2)}=1$ (the minimum) if and only if $\gamma^{(1,1)}=0$, and then $c^{(2,2)}=0$.
--
--   **Formalization Note** The paper's words "complete lack of fourth-order coherence" for $\gamma^{(2,2)}=2$ and "complete coherence of intensity distributions" for $\gamma^{(2,2)}=1$ are terminology; the statement records the corresponding equalities.
-- source:
--   Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, On the van Cittert - Zernike theorem for intensity correlations and its applications, arXiv:1706.02824v1 (2017), claim c015; Section 5, eq. (21) and the following paragraph, PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace Arxiv1706_02824

theorem eq21_fourth_order_coherence_factor {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (V : ℝ → Omega → ℂ) (hV : IsCircularGaussian P V)
    (x1 x2 : ℝ) (h1 : 0 < meanIntensity P V x1) (h2 : 0 < meanIntensity P V x2) :
    coherenceFactor22 P V x1 x2 = 1 + intensityCorrCoeff P V x1 x2 ∧
    1 ≤ coherenceFactor22 P V x1 x2 ∧ coherenceFactor22 P V x1 x2 ≤ 2 ∧
    (coherenceFactor22 P V x1 x2 = 2 ↔ ‖coherenceFactor11 P V x1 x2‖ = 1) ∧
    (coherenceFactor22 P V x1 x2 = 1 ↔ coherenceFactor11 P V x1 x2 = 0) ∧
    (coherenceFactor22 P V x1 x2 = 1 → intensityCorrCoeff P V x1 x2 = 0) := by sorry

end Arxiv1706_02824
