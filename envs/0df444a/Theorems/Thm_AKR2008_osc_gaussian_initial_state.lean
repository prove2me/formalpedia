-- Prove2me | Theorems.Thm_AKR2008_osc_gaussian_initial_state
-- name    : AKR2008.osc_gaussian_initial_state
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T00:05:37.530835+00:00
-- url     : https://prove2.me/theorems/3e4c6f1e-d2fe-4378-a5c8-c3420d09f094
-- title:
--   Appendix A: at $t=0$, $\langle p\rangle=0$, $\Delta p=0$, $\langle x\rangle=w$, $\Delta x=\tau^{-1/2}$
-- statement:
--   Let $\omega,w$ be real and $\tau>0$, and let $P_{\mathrm{osc}}$, $S_{\mathrm{osc}}$ be as in Appendix A. At $t=0$:
--
--   1. $P_{\mathrm{osc}}(\cdot,0)$ is normalized: $\int P_{\mathrm{osc}}(x,0)\,dx=1$;
--   2. average position $\langle x\rangle(0)=\int x\,P_{\mathrm{osc}}(x,0)\,dx=w$;
--   3. position uncertainty $\Delta x(0)=\Bigl(\int (x-w)^2P_{\mathrm{osc}}(x,0)\,dx\Bigr)^{1/2}=\tau^{-1/2}$;
--   4. average momentum $\langle p\rangle(0)=\int P_{\mathrm{osc}}(x,0)\,\frac{\partial S_{\mathrm{osc}}}{\partial x}(x,0)\,dx=0$;
--   5. no momentum uncertainty: $\int P_{\mathrm{osc}}(x,0)\bigl(\frac{\partial S_{\mathrm{osc}}}{\partial x}(x,0)\bigr)^2dx=0$, i.e. $\Delta p(0)=0$.
--
--   Thus the Gaussian ensemble is prepared with zero momentum and no momentum uncertainty, but localized in space — the interpretation the paper transfers to the classical sector of the hybrid model.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), https://doi.org/10.1103/PhysRevD.78.064051, p. 064051-15, Appendix A

import Mathlib
import Definitions.Def_AKR2008_HybridDefs

namespace AKR2008

theorem osc_gaussian_initial_state (ω τ w : ℝ) (hτ : 0 < τ) :
    ∫ x, oscP ω τ w x 0 = 1 ∧
    ∫ x, x * oscP ω τ w x 0 = w ∧
    Real.sqrt (∫ x, (x - w) ^ 2 * oscP ω τ w x 0) = τ ^ (-(1 / 2 : ℝ)) ∧
    ∫ x, oscP ω τ w x 0 * deriv (fun y => oscS ω y 0) x = 0 ∧
    ∫ x, oscP ω τ w x 0 * (deriv (fun y => oscS ω y 0) x) ^ 2 = 0 := by sorry

end AKR2008
