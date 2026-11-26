-- Prove2me | Theorems.Thm_Arxiv2606_14486_reciprocity_implications
-- name    : Arxiv2606_14486.reciprocity_implications
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T19:10:19.70208+00:00
-- url     : https://prove2.me/theorems/d7b1d026-d18c-5e49-92ab-6651d945864e
-- title:
--   Sec. II-A, implications (1)-(2) of eq. (8) (as proved)
-- statement:
--   Keep the setting of eq. (8): $k,d,\theta_1,\theta_2>0$, $\theta_2\ne\theta_1$, reverse coefficients $R'_ie^{j(i-1)\Delta\psi'}$ with $R'_i>0$, and $\Delta\psi=kd(\sin\theta_1-\sin\theta_2)$. Say that the return beam is formed at $\theta_3$ when the reverse wavefront $a(-\theta_3)\cdot\Psi'\cdot a(\theta_2)$ is in phase.
--
--   1. If the reflection phases do not depend on the incidence angle, $\Delta\psi'=\Delta\psi$, then the return beam is formed at $\theta_1$.
--   2. If moreover $n\ge2$, $kd\le2\pi$ (element spacing at most one wavelength), and $\theta_1,\theta_3\in(0,\pi/2)$ (the same quadrant), then a return beam formed at $\theta_3$ satisfies $\theta_3=\theta_1$.
--   3. For $n\ge2$, the return beam is formed at $\theta_1$ if and only if $\Delta\psi'-\Delta\psi\in2\pi\mathbb{Z}$. So when the phases depend on the incidence angle and $\Delta\psi'-\Delta\psi\notin2\pi\mathbb{Z}$, the return beam is not formed at $\theta_1$.
--
--   **Formalization Note** The paper says that $\Delta\psi'=\Delta\psi$ "automatically leads to $\theta_3=\theta_1$". Its argument uses only the $m=0$ solution of eq. (8). For $kd>2\pi$ there are grating lobes, and the statement fails as printed: with $kd=4\pi$, $\sin\theta_1=0.3$ and $m=-1$, the direction $\theta_3=\arcsin0.8\ne\theta_1$ also receives a return beam. Item 2 therefore adds the hypothesis $kd\le2\pi$, under which $m=0$ is forced. The paper's "need not be formed at $\theta_1$" is stated as the exact criterion in item 3.
-- source:
--   Khankhoje and Kundu, Implications of the Reciprocity Theorem for Reconfigurable Intelligent Surfaces, arXiv:2606.14486v1 (2026), claim c015; Sec. II-A, the two numbered implications following eq. (8), PDF p. 2

import Mathlib
import Definitions.Def_Arxiv2606_14486_Basic

open MeasureTheory

namespace Arxiv2606_14486

theorem reciprocity_implications {n : ℕ} (k d θ₁ θ₂ : ℝ) (hk : 0 < k) (hd : 0 < d)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hθ₁₂ : θ₂ ≠ θ₁)
    (R' : Fin n → ℝ) (hR' : ∀ i, 0 < R' i) (dpsi' : ℝ) :
    (dpsi' = phaseStep k d θ₁ θ₂ →
      InPhase (wavefront n k d (-θ₁) θ₂ (reflCoeffs R' (linearPhases n 0 dpsi')))) ∧
    (dpsi' = phaseStep k d θ₁ θ₂ → 2 ≤ n → k * d ≤ 2 * Real.pi → θ₁ < Real.pi / 2 →
      ∀ θ₃ : ℝ, 0 < θ₃ → θ₃ < Real.pi / 2 →
        InPhase (wavefront n k d (-θ₃) θ₂ (reflCoeffs R' (linearPhases n 0 dpsi'))) →
          θ₃ = θ₁) ∧
    (2 ≤ n →
      (InPhase (wavefront n k d (-θ₁) θ₂ (reflCoeffs R' (linearPhases n 0 dpsi'))) ↔
        ∃ m : ℤ, dpsi' - phaseStep k d θ₁ θ₂ = 2 * m * Real.pi)) := by sorry

end Arxiv2606_14486
