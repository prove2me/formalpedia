-- Prove2me | Theorems.Thm_FaulhuberTFA_stft_covariance
-- name    : FaulhuberTFA.stft_covariance
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T11:26:21.821814+00:00
-- url     : https://prove2.me/theorems/83feee6f-951c-4336-ac64-288181719ff5
-- title:
--   Proposition 2.6: covariance principle for the STFT
-- statement:
--   Let $f,g\in L^2(\mathbb{R}^d)$. For all $x,\xi,\omega,\eta\in\mathbb{R}^d$,
--
--   $$V_g(M_\eta T_\xi f)(x,\omega)=e^{-2\pi i\xi\cdot(\omega-\eta)}\,V_gf(x-\xi,\omega-\eta),$$
--
--   where $(T_\xi f)(t)=f(t-\xi)$ and $(M_\eta f)(t)=e^{2\pi i\eta\cdot t}f(t)$.
--
--   A time-frequency shift of the signal by $(\xi,\eta)$ translates its STFT by $(\xi,\eta)$, up to a phase factor.
-- source:
--   Faulhuber, Time-Frequency Analysis (Lecture Notes), arXiv:2204.01596 (2022), Chapter 2, Proposition 2.6, eq. (2.3), p. 19

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

namespace FaulhuberTFA

theorem stft_covariance {d : ℕ} {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (x ξ ω η : Rd d) :
    stft g (modul η (transl ξ f)) x ω = ePhase (-⟪ξ, ω - η⟫_ℝ) * stft g f (x - ξ) (ω - η) := by sorry

end FaulhuberTFA
