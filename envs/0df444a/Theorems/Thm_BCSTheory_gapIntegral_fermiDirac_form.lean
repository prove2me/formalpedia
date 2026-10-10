-- Prove2me | Theorems.Thm_BCSTheory_gapIntegral_fermiDirac_form
-- name    : BCSTheory.gapIntegral_fermiDirac_form
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:24:23.903781+00:00
-- url     : https://prove2.me/theorems/6320e495-3193-4490-9c35-10570155730e
-- title:
--   Gap equation: Fermi–Dirac form equals tanh form
-- statement:
--   For $k_B>0$, $T>0$ and all real $\hbar\omega_D$, $\Delta$, with $f(E,T)=1/(e^{E/k_BT}+1)$, $$\int_0^{\hbar\omega_D}\frac{d\eta}{\sqrt{\eta^2+\Delta^2}}\Bigl[1-2f\bigl(\sqrt{\eta^2+\Delta^2},T\bigr)\Bigr] = \int_0^{\hbar\omega_D}\frac{d\eta}{\sqrt{\eta^2+\Delta^2}}\tanh\frac{\sqrt{\eta^2+\Delta^2}}{2k_BT}.$$
-- source:
--   Wikipedia (de), Artikel „BCS-Theorie“ (PDF-Ausdruck vom 05.10.2026), Abschnitt „Erfolge der BCS-Theorie“, Unterabschnitt „Existenz einer Energielücke“, Integralgleichung für $T \neq 0$ und ihre tanh-Form.

import Mathlib
import Definitions.Def_BCSTheory_GapEquation
open Filter Topology

namespace BCSTheory

theorem gapIntegral_fermiDirac_form (kB hbarOmegaD Δ T : ℝ) (hkB : 0 < kB) (hT : 0 < T) :
    (∫ η in (0 : ℝ)..hbarOmegaD,
        (1 - 2 * fermiDirac kB (quasiparticleEnergy η Δ) T) / quasiparticleEnergy η Δ) =
      gapIntegral kB hbarOmegaD Δ T := by sorry

end BCSTheory
