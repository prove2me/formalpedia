-- Prove2me | Theorems.Thm_AKR2008_osc_gaussian_energy
-- name    : AKR2008.osc_gaussian_energy
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-28T00:07:35.199143+00:00
-- url     : https://prove2.me/theorems/0573af0e-465f-4019-8ea2-15f1d01d6bf7
-- title:
--   Appendix A: energy $E=\langle-\partial_tS_{\mathrm{osc}}\rangle$ of the Gaussian ensemble (corrected form)
-- statement:
--   Let $\omega,w$ be real, $\tau>0$, and $t$ a time with $\cos(\omega t)\ne0$. For the Gaussian ensemble of Appendix A,
--   $$E=\Bigl\langle-\frac{\partial S_{\mathrm{osc}}}{\partial t}\Bigr\rangle=\int_{\mathbb R}P_{\mathrm{osc}}(x,t)\Bigl(-\frac{\partial S_{\mathrm{osc}}}{\partial t}(x,t)\Bigr)dx=\frac12\,\omega^2\bigl(\tau^{-1}+w^2\bigr).$$
--   In particular $E$ is independent of $t$.
--
--   The paper prints $E=\frac12\omega^2\tau^{-1}$, which agrees with the displayed value exactly when $w=0$. For $w\ne0$ the ensemble has mean-square position $w^2+\tau^{-1}$ at $t=0$, and the printed value omits the $w^2$ term. The milestone is stated in this corrected form so that it is not a false target.
--
--   **Formalization Note** $\partial_tS_{\mathrm{osc}}$ is the one-variable derivative in $t$; the integral is the Lebesgue integral over $\mathbb R$.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), https://doi.org/10.1103/PhysRevD.78.064051, p. 064051-15, Appendix A (total energy; corrected for w ≠ 0)

import Mathlib
import Definitions.Def_AKR2008_HybridDefs

namespace AKR2008

theorem osc_gaussian_energy (ω τ w t : ℝ) (hτ : 0 < τ) (hcos : Real.cos (ω * t) ≠ 0) :
    ∫ x, oscP ω τ w x t * (-deriv (fun s => oscS ω x s) t) = ω ^ 2 * (τ⁻¹ + w ^ 2) / 2 := by
  sorry

end AKR2008
