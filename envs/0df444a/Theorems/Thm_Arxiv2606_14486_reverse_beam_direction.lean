-- Prove2me | Theorems.Thm_Arxiv2606_14486_reverse_beam_direction
-- name    : Arxiv2606_14486.reverse_beam_direction
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:09:46.758071+00:00
-- url     : https://prove2.me/theorems/268ade3c-5aa0-416c-a132-9d0598ed7960
-- title:
--   Eqs. (7)-(8): phases of the reverse wavefront and the reverse beam direction
-- statement:
--   In the setting of eq. (4), let the wave arrive from the reverse direction $\theta_2$, with $\theta_2\ne\theta_1$, and consider a direction $\theta_3>0$. Under this illumination the element coefficients are $R'_ie^{j\psi'_i}$ with $R'_i>0$ and $\psi'_i=(i-1)\Delta\psi'$ (eq. 6). The reverse wavefront $z=a(-\theta_3)\cdot\Psi'\cdot a(\theta_2)$ is then
--
--   $$z_i=R'_i\exp\Big(j(i-1)\big[kd(\sin\theta_2-\sin\theta_3)+\Delta\psi'\big]\Big)\qquad\text{(eq. 7)}.$$
--
--   If the array has $n\ge2$ elements and the $z_i$ are all in phase (constructive interference at $\theta_3$), then for some integer $m$
--
--   $$\sin\theta_3=\sin\theta_1+\frac{(\Delta\psi'-\Delta\psi)-2m\pi}{kd}\qquad\text{(eq. 8)},$$
--
--   where $\Delta\psi=kd(\sin\theta_1-\sin\theta_2)$.
--
--   **Formalization Note** The paper writes eq. (7) for $\arg z_i$ modulo $2\pi$; here it is the exact identity for $z_i$. The hypotheses $n\ge2$ and $R'_i>0$ are implicit in the paper. For $n=1$ every wavefront is in phase and eq. (8) can fail. The paper's remark that the $2m\pi$ term "ensures a real value for $\theta_3$" is not formalized.
-- source:
--   Khankhoje and Kundu, Implications of the Reciprocity Theorem for Reconfigurable Intelligent Surfaces, arXiv:2606.14486v1 (2026), claim c014; Sec. II-A, eqs. (5)-(8), PDF p. 2

import Mathlib
import Definitions.Def_Arxiv2606_14486_Basic

open MeasureTheory

namespace Arxiv2606_14486

theorem reverse_beam_direction {n : ℕ} (k d θ₁ θ₂ θ₃ : ℝ) (hk : 0 < k) (hd : 0 < d)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hθ₃ : 0 < θ₃) (hθ₁₂ : θ₂ ≠ θ₁)
    (R' : Fin n → ℝ) (hR' : ∀ i, 0 < R' i) (dpsi' : ℝ) :
    (∀ i : Fin n, wavefront n k d (-θ₃) θ₂ (reflCoeffs R' (linearPhases n 0 dpsi')) i =
      (R' i : ℂ) * Complex.exp
        ((((i : ℕ) : ℝ) * (k * d * (Real.sin θ₂ - Real.sin θ₃) + dpsi') : ℝ) * Complex.I)) ∧
    (2 ≤ n → InPhase (wavefront n k d (-θ₃) θ₂ (reflCoeffs R' (linearPhases n 0 dpsi'))) →
      ∃ m : ℤ, Real.sin θ₃ =
        Real.sin θ₁ + ((dpsi' - phaseStep k d θ₁ θ₂) - 2 * m * Real.pi) / (k * d)) := by sorry

end Arxiv2606_14486
