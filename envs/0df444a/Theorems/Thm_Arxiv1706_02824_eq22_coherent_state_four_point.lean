-- Prove2me | Theorems.Thm_Arxiv1706_02824_eq22_coherent_state_four_point
-- name    : Arxiv1706_02824.eq22_coherent_state_four_point
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T01:20:00.337919+00:00
-- url     : https://prove2.me/theorems/af2bc417-0519-453f-8c34-aad99bb511fb
-- title:
--   Eq. (22): four-point field correlation in a coherent state
-- statement:
--   Consider a single mode with angular frequency $\omega>0$ and mode function $u_0$ in the source plane, normalised by $\int|u_0|^2=1$, with $E_0^+(x)=i(\hbar\omega/2)^{1/2}u_0(x)a$ and $E_0^-=(E_0^+)^\dagger$. For the Glauber coherent state $|\alpha\rangle$ and all $x_1',\dots,x_4'$,
--   $$\langle\alpha|E_0^-(x_1')E_0^+(x_2')E_0^-(x_3')E_0^+(x_4')|\alpha\rangle=(\hbar\omega/2)^2\big(|\alpha|^4+|\alpha|^2\big)\,u_0^*(x_1')u_0(x_2')u_0^*(x_3')u_0(x_4').$$
--
--   This is the quantised analogue of the four-point correlation (2). The term $|\alpha|^2$ comes from the operator ordering.
--
--   **Formalization Note** Operators act on Fock coefficients, and $|\alpha\rangle$ is given by its Fock expansion.
-- source:
--   Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, On the van Cittert - Zernike theorem for intensity correlations and its applications, arXiv:1706.02824v1 (2017), claim c031; Section 6, eq. (22), PDF pp. 5-6

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace Arxiv1706_02824

theorem eq22_coherent_state_four_point (hbar ω : ℝ) (hhbar : 0 < hbar) (hω : 0 < ω)
    (u0 : ℝ → ℂ) (hnorm : ∫ y : ℝ, ‖u0 y‖ ^ 2 = 1) (α : ℂ) (x1 x2 x3 x4 : ℝ) :
    cohExpect α (fun ψ => fieldNeg hbar ω u0 x1 (fieldPos hbar ω u0 x2
      (fieldNeg hbar ω u0 x3 (fieldPos hbar ω u0 x4 ψ)))) =
      (((hbar * ω / 2) ^ 2 * (‖α‖ ^ 4 + ‖α‖ ^ 2) : ℝ) : ℂ) *
        conj (u0 x1) * u0 x2 * conj (u0 x3) * u0 x4 := by sorry

end Arxiv1706_02824
