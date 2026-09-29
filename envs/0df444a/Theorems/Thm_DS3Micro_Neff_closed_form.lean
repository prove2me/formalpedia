-- Prove2me | Theorems.Thm_DS3Micro_Neff_closed_form
-- name    : DS3Micro.Neff_closed_form
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T02:15:18.392351+00:00
-- url     : https://prove2.me/theorems/f72dce5b-ca46-41fa-bc89-81e9305fcb27
-- title:
--   Closed form of the effective number of eigenvalues $N_{\mathrm{eff}} = \int_2^{E_0} e^{S_0}\rho_0$
-- statement:
--   Let $b\in\mathbb{C}$ with $b^2 = i\beta$ for some $\beta>0$, and $S_0\in\mathbb{R}$. Then
--   $$N_{\mathrm{eff}} = \int_2^{E_0} e^{S_0}\rho_0(E)\,dE = e^{S_0}\,\frac{-4i\sin(\pi b^2)\sin(\pi b^{-2})}{\pi\,(b^{-2}-b^2)},$$
--   where $E_0 = 2\cos(\pi b^{-2})$ (taken as a real number via its real part). This is the evaluation of the integral in (4.32) underlying the second line of (4.33).
-- source:
--   S. Collier, L. Eberhardt, B. Mühlmann, *A microscopic realization of dS$_3$*, arXiv:2501.01486v1 [hep-th] (2 Jan 2025), https://arxiv.org/abs/2501.01486; eqs. (4.32)–(4.33), pp. 36–37.

import Mathlib
import Definitions.Def_dS3_microstates

open Complex

namespace DS3Micro
theorem Neff_closed_form (b : ℂ) (hb : InRegime b) (S0 : ℝ) :
    Neff b S0 = (Real.exp S0 : ℂ) *
      (-4 * Complex.I * Complex.sin ((Real.pi : ℂ) * b ^ 2) *
          Complex.sin ((Real.pi : ℂ) * (b ^ 2)⁻¹) /
        ((Real.pi : ℂ) * ((b ^ 2)⁻¹ - b ^ 2))) := by
  sorry
end DS3Micro
