-- Prove2me | Theorems.Thm_FaulhuberTFA_crossAmbiguity_covariance
-- name    : FaulhuberTFA.crossAmbiguity_covariance
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T11:53:15.083152+00:00
-- url     : https://prove2.me/theorems/325bf1c7-e680-43ff-92ed-c4a57ea0b0bf
-- title:
--   Covariance of the cross-ambiguity function under time-frequency shifts
-- statement:
--   Let $f,g\in L^2(\mathbb{R}^d)$ and $x,\omega,\xi_1,\xi_2,\eta_1,\eta_2\in\mathbb{R}^d$. Then
--
--   $$A(M_{\eta_1}T_{\xi_1}f,\,M_{\eta_2}T_{\xi_2}g)(x,\omega)=e^{\pi i x\cdot(\eta_1+\eta_2)}\,e^{-\pi i\omega\cdot(\xi_1+\xi_2)}\,e^{\pi i(\eta_1-\eta_2)\cdot(\xi_1+\xi_2)}\,A(f,g)(x-\xi_1+\xi_2,\,\omega-\eta_1+\eta_2).$$
--
--   Time-frequency shifts of the two arguments translate the cross-ambiguity function by the difference of the shifts, up to an explicit phase.
-- source:
--   Faulhuber, Time-Frequency Analysis (Lecture Notes), arXiv:2204.01596 (2022), Section 3.3, covariance display at the end of the section, p. 30

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

namespace FaulhuberTFA

theorem crossAmbiguity_covariance {d : ℕ} {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (x ω ξ₁ ξ₂ η₁ η₂ : Rd d) :
    crossAmbiguity (modul η₁ (transl ξ₁ f)) (modul η₂ (transl ξ₂ g)) x ω =
      ePhase (⟪x, η₁ + η₂⟫_ℝ / 2) * ePhase (-⟪ω, ξ₁ + ξ₂⟫_ℝ / 2) * ePhase (⟪η₁ - η₂, ξ₁ + ξ₂⟫_ℝ / 2) *
        crossAmbiguity f g (x - ξ₁ + ξ₂) (ω - η₁ + η₂) := by sorry

end FaulhuberTFA
