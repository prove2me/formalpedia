-- Prove2me | Theorems.Thm_Arxiv2606_14486_reciprocity_integral_vanishes
-- name    : Arxiv2606_14486.reciprocity_integral_vanishes
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:12:17.491803+00:00
-- url     : https://prove2.me/theorems/a6b69a0e-23c0-46c6-83c6-f9633658404a
-- title:
--   Eq. (12): the source-free reciprocity integral over a surface enclosing the RIS vanishes
-- statement:
--   Let $V=\prod_{i=1}^3(a_i,b_i)$ be an open rectangular box with $a_i<b_i$ and boundary surface $S$, and let $\omega>0$. Inside $V$, let the medium be linear and reciprocal: its permittivity and permeability tensors $\varepsilon(x),\mu(x)\in\mathbb{C}^{3\times3}$ are symmetric, $\varepsilon^T=\varepsilon$ and $\mu^T=\mu$. Let $(E_1,H_1)$ and $(E_2,H_2)$ be time-harmonic phasor fields (time dependence $e^{j\omega t}$). Assume they are continuous on the closed box, differentiable in $V$, and satisfy the source-free Maxwell equations
--
--   $$\nabla\times E_m=-j\omega\mu H_m,\qquad \nabla\times H_m=j\omega\varepsilon E_m\qquad(m=1,2)$$
--
--   at every point of $V$. Then
--
--   $$\Psi=\oint_S\big(E_1\times H_2-E_2\times H_1\big)\cdot d\vec s=0.$$
--
--   In the paper, $(E_1,H_1)$ and $(E_2,H_2)$ are the fields with the transmitter at $A$ and at $B$, and $S$ is the bounding box that just encloses the RIS. This is the source-free reciprocity theorem (Harrington, Eq. 3-34) on which the paper's second numerical experiment rests.
--
--   **Formalization Note** The surface integral is the sum of the six face integrals with outward normals, and the products are bilinear, with no complex conjugation. The fields are taken to be classically differentiable throughout the box, as in Harrington's derivation. Fields with jumps across material interfaces or perfect conductors inside the box, as in the paper's actual RIS, are not covered by this formulation.
-- source:
--   Khankhoje and Kundu, Implications of the Reciprocity Theorem for Reconfigurable Intelligent Surfaces, arXiv:2606.14486v1 (2026), claim c019; Sec. III, 'Second experiment -- reciprocity theorem', eq. (12) (citing Harrington, Eq. 3-34), PDF p. 4; bounding box: Appendix A, 'Finite RIS specifications', PDF p. 5

import Mathlib
import Definitions.Def_Arxiv2606_14486_Basic

open MeasureTheory

namespace Arxiv2606_14486

theorem reciprocity_integral_vanishes (a b : Fin 3 → ℝ) (hab : ∀ i, a i < b i)
    (ω : ℝ) (hω : 0 < ω) (eps mu : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
    (hmed : IsReciprocalMedium eps mu (boxInterior a b))
    (E₁ H₁ E₂ H₂ : (Fin 3 → ℝ) → Fin 3 → ℂ)
    (hE₁ : ContinuousOn E₁ (Set.Icc a b)) (hH₁ : ContinuousOn H₁ (Set.Icc a b))
    (hE₂ : ContinuousOn E₂ (Set.Icc a b)) (hH₂ : ContinuousOn H₂ (Set.Icc a b))
    (h₁ : IsSourceFreeMaxwellOn ω eps mu (boxInterior a b) E₁ H₁)
    (h₂ : IsSourceFreeMaxwellOn ω eps mu (boxInterior a b) E₂ H₂) :
    reciprocityIntegral a b E₁ H₁ E₂ H₂ = 0 := by sorry

end Arxiv2606_14486
