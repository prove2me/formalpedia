-- Prove2me | Theorems.Thm_DS3Micro_first_zero
-- name    : DS3Micro.first_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T02:14:45.313211+00:00
-- url     : https://prove2.me/theorems/8a5bdf8a-962e-4ab3-bb4d-069e103a2567
-- title:
--   $E_0 = 2\cos(\pi b^{-2})$ is the first zero of the eigenvalue density $\rho_0$ above $E=2$
-- statement:
--   Let $b\in\mathbb{C}$ with $b^2 = i\beta$ for some $\beta>0$. Then $E_0 = 2\cos(\pi b^{-2})$ is a real number with $E_0>2$; the eigenvalue density $\rho_0(E) = \frac{2}{\pi}\sinh(-i\pi b^2)\sin(-ib^2\operatorname{arccosh}(E/2))$ vanishes at $E=E_0$; and for every real $E$ with $2<E<E_0$, $\rho_0(E)$ is real and strictly positive. Thus $[2,E_0]$ is the first interval of positivity of the density, as used in §4.4 and Appendix C.
-- source:
--   S. Collier, L. Eberhardt, B. Mühlmann, *A microscopic realization of dS$_3$*, arXiv:2501.01486v1 [hep-th] (2 Jan 2025), https://arxiv.org/abs/2501.01486; §4.4 (p. 36): "this interval is $2\le E\le E_0 = 2\cos(\pi b^{-2})$"; Appendix C (p. 61): the density (C.4) "is initially positive for $E\ge 2$ … goes to zero at $E_0 = 2\cos(\pi b^{-2})$".

import Mathlib
import Definitions.Def_dS3_microstates

open Complex

namespace DS3Micro
theorem first_zero (b : ℂ) (hb : InRegime b) :
    (E0 b).im = 0 ∧ 2 < (E0 b).re ∧ rho0 b (E0 b).re = 0 ∧
      ∀ E : ℝ, 2 < E → E < (E0 b).re → (rho0 b E).im = 0 ∧ 0 < (rho0 b E).re := by
  sorry
end DS3Micro
