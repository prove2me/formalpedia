-- Prove2me | Theorems.Thm_DS3Micro_entropy_formula
-- name    : DS3Micro.entropy_formula
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T02:15:45.192967+00:00
-- url     : https://prove2.me/theorems/1348bb64-ec66-4e51-9860-b7b086e24e57
-- title:
--   Microscopic de Sitter entropy: $S^{\mathrm{micro}}_{\mathrm{dS}} = 2S_0 + 2\log(\cdots) = 2\log\big(T^{(b)}_{1,1}/2\pi i\big)$
-- statement:
--   Let $b\in\mathbb{C}$ with $b^2 = i\beta$ for some $\beta>0$, and $S_0\in\mathbb{R}$. With $S^{\mathrm{micro}}_{\mathrm{dS}} = 2\log N_{\mathrm{eff}}$ (complex principal logarithm),
--   $$S^{\mathrm{micro}}_{\mathrm{dS}} = 2S_0 + 2\log\Big(\frac{-4i\sin(\pi b^2)\sin(\pi b^{-2})}{\pi(b^{-2}-b^2)}\Big) \quad\text{and}\quad S^{\mathrm{micro}}_{\mathrm{dS}} = 2\log\Big(\frac{1}{2\pi i}T^{(b)}_{1,1}\Big),$$
--   where $T^{(b)}_{1,1} = e^{S_0}\,\frac{8b^2\sin(\pi b^2)\sin(\pi b^{-2})}{1-b^4}$ is the tension of the first ZZ-instanton. These are the two equalities of (4.33).
-- source:
--   S. Collier, L. Eberhardt, B. Mühlmann, *A microscopic realization of dS$_3$*, arXiv:2501.01486v1 [hep-th] (2 Jan 2025), https://arxiv.org/abs/2501.01486; eqs. (4.33)–(4.34), p. 37.

import Mathlib
import Definitions.Def_dS3_microstates

open Complex

namespace DS3Micro
theorem entropy_formula (b : ℂ) (hb : InRegime b) (S0 : ℝ) :
    SdSMicro b S0 = 2 * (S0 : ℂ) + 2 * Complex.log
        (-4 * Complex.I * Complex.sin ((Real.pi : ℂ) * b ^ 2) *
            Complex.sin ((Real.pi : ℂ) * (b ^ 2)⁻¹) /
          ((Real.pi : ℂ) * ((b ^ 2)⁻¹ - b ^ 2))) ∧
      SdSMicro b S0 = 2 * Complex.log (tension b S0 / (2 * (Real.pi : ℂ) * Complex.I)) := by
  sorry
end DS3Micro
