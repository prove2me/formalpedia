-- Prove2me | Theorems.Thm_Arxiv1506_07229_zero_condition_from_array_permittivity
-- name    : Arxiv1506_07229.zero_condition_from_array_permittivity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:04:06.227801+00:00
-- url     : https://prove2.me/theorems/bb19e063-462f-4fac-b887-4a3adfdde6d9
-- title:
--   Eq. (11) (as proved): $1/\varepsilon=0$ exactly when $1/\varepsilon_{3D}=1-\frac{2}{qd}\frac{e^{qd}-1}{e^{qd}+1}$
-- statement:
--   Let $q>0$, $d>0$, and let $\varepsilon_{3D}\neq0$ be the complex permittivity of the array of layers with separation $d$. Let $1/\varepsilon$ be given by the approximate relation (10). Then
--
--   $$\frac1\varepsilon=0\iff\frac{1}{\varepsilon_{3D}}=1-\frac{2}{qd}\,\frac{e^{qd}-1}{e^{qd}+1}.$$
--
--   **Formalization Note** The paper prints Eq. (11) as $\varepsilon_{3D}=1-\frac{2}{qd}\frac{e^{qd}-1}{e^{qd}+1}$. Solving Eq. (10) for $1/\varepsilon=0$ gives this expression as the value of $1/\varepsilon_{3D}$, not of $\varepsilon_{3D}$. At $qd=3.04$ the printed right-hand side is $0.402$. With $\varepsilon_{3D}=0.402$, Eq. (10) gives $1/\varepsilon=2.84$, not $0$. The statement is the condition the derivation establishes. The misprint is in (11), not in (10): to leading order Eq. (10) gives $1/\varepsilon-1\approx\frac{qd}{2}(1/\varepsilon_{3D}-1)$, the correct dilution relation for a layer in an array, so (10) as printed is physically right.
-- source:
--   V. U. Nazarov, Negative static permittivity and violation of Kramers-Kronig relations in quasi-two-dimensional crystals, arXiv:1506.07229v3 (2015), claim c008; main text, Eqs. (10) and (11), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv1506_07229_Basic

open MeasureTheory Filter Topology Real ComplexConjugate

namespace Arxiv1506_07229

theorem zero_condition_from_array_permittivity (q d : ℝ) (hq : 0 < q) (hd : 0 < d)
    (eps3D : ℂ) (h0 : eps3D ≠ 0) :
    invEpsFrom3D q d eps3D = 0 ↔
      eps3D⁻¹ = ((1 - 2 / (q * d) * ((Real.exp (q * d) - 1) / (Real.exp (q * d) + 1)) : ℝ) : ℂ) := by sorry

end Arxiv1506_07229
