-- Prove2me | Theorems.Thm_FaulhuberTFA_crossAmbiguity_covariance_diag
-- name    : FaulhuberTFA.crossAmbiguity_covariance_diag
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T11:53:43.101949+00:00
-- url     : https://prove2.me/theorems/2611fcf7-5140-460f-aaa2-db499dc5f9db
-- title:
--   Shifting both arguments only adds a phase
-- statement:
--   Let $f,g\in L^2(\mathbb{R}^d)$ and $x,\omega,\xi,\eta\in\mathbb{R}^d$. Then
--
--   $$A(M_\eta T_\xi f,\,M_\eta T_\xi g)(x,\omega)=e^{2\pi i(x\cdot\eta-\omega\cdot\xi)}\,A(f,g)(x,\omega).$$
--
--   Shifting both signals by the same point of the time-frequency plane changes their cross-ambiguity function only by a phase factor.
-- source:
--   Faulhuber, Time-Frequency Analysis (Lecture Notes), arXiv:2204.01596 (2022), Section 3.3, the special case stated right after the covariance display, p. 30

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

namespace FaulhuberTFA

theorem crossAmbiguity_covariance_diag {d : ℕ} {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (x ω ξ η : Rd d) :
    crossAmbiguity (modul η (transl ξ f)) (modul η (transl ξ g)) x ω =
      ePhase (⟪x, η⟫_ℝ - ⟪ω, ξ⟫_ℝ) * crossAmbiguity f g x ω := by sorry

end FaulhuberTFA
