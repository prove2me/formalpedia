-- Prove2me | Theorems.Thm_DS3Micro_entropy_matches_sphere
-- name    : DS3Micro.entropy_matches_sphere
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T02:39:36.227009+00:00
-- url     : https://prove2.me/theorems/dbda0802-6003-48dd-9826-8f13c0f536c1
-- title:
--   Microscopic dS$_3$ entropy: $2\log N_{\mathrm{eff}} = \log|Z^{S^3}_{\mathrm{grav}}| + \text{const}$
-- statement:
--   Let $K>0$ and let $Z(b,S_0)$ be any complex-valued function of $b\in\mathbb{C}$ and $S_0\in\mathbb{R}$ such that, for every admissible $b$ ($b^2 = i\beta$ with $\beta>0$) and every $S_0$,
--   $$|Z(b,S_0)| = K\,\Big|e^{2S_0}\,\frac{\sin(\pi b^2)^2\sin(\pi b^{-2})^2}{(b^{-2}-b^2)^2}\Big|,$$
--   i.e. $Z$ satisfies eq. (4.5), $Z^{S^3}_{\mathrm{grav}}\sim e^{2S_0}\sin(\pi b^2)^2\sin(\pi b^{-2})^2/(b^{-2}-b^2)^2$ up to a $b$-independent constant. Then there is a real constant $c$ such that for all admissible $b$ and all $S_0$,
--   $$S^{\mathrm{micro}}_{\mathrm{dS}}(b,S_0) = 2\log N_{\mathrm{eff}}(b,S_0) = \log|Z(b,S_0)| + c.$$
--   This is the matching (4.35), $S^{\mathrm{micro}}_{\mathrm{dS}} = \log|Z^{S^3}_{\mathrm{grav}}|$, up to the order-one constant that the paper fixes afterwards in (4.37).
-- source:
--   S. Collier, L. Eberhardt, B. Mühlmann, *A microscopic realization of dS$_3$*, arXiv:2501.01486v1 [hep-th] (2 Jan 2025), https://arxiv.org/abs/2501.01486; eq. (4.35), p. 37, using (4.5) p. 27; see also eq. (1.1), p. 3.

import Mathlib
import Definitions.Def_dS3_microstates

open Complex

namespace DS3Micro
theorem entropy_matches_sphere (K : ℝ) (hK : 0 < K) (Z : ℂ → ℝ → ℂ)
    (hZ : ∀ (b : ℂ) (S0 : ℝ), InRegime b →
      ‖Z b S0‖ = K * ‖(Real.exp (2 * S0) : ℂ) *
        (Complex.sin ((Real.pi : ℂ) * b ^ 2) ^ 2 * Complex.sin ((Real.pi : ℂ) * (b ^ 2)⁻¹) ^ 2 /
          ((b ^ 2)⁻¹ - b ^ 2) ^ 2)‖) :
    ∃ c : ℝ, ∀ (b : ℂ) (S0 : ℝ), InRegime b →
      SdSMicro b S0 = (Real.log ‖Z b S0‖ : ℂ) + (c : ℂ) := by
  sorry
end DS3Micro
