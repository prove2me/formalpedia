-- Prove2me | Theorems.Thm_BCSTheory_zeroTemperatureGap_eq
-- name    : BCSTheory.zeroTemperatureGap_eq
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:23:08.803508+00:00
-- url     : https://prove2.me/theorems/3a05bb49-b948-4817-b7b8-9b36228c597a
-- title:
--   Explicit zero-temperature gap $\Delta(0) = \hbar\omega_D / \sinh(1/V_0 Z(E_F))$
-- statement:
--   Let $\hbar\omega_D>0$ and $\lambda = V_0 Z(E_F) > 0$. A number $\Delta>0$ solves the zero-temperature gap equation $\frac{1}{\lambda} = \int_0^{\hbar\omega_D} \frac{d\eta}{\sqrt{\eta^2+\Delta^2}}$ if and only if $\Delta = \hbar\omega_D/\sinh(1/\lambda)$; consequently $\Delta(0) = \hbar\omega_D/\sinh(1/\lambda)$.
-- source:
--   Wikipedia (de), Artikel „BCS-Theorie“ (PDF-Ausdruck vom 05.10.2026), Abschnitt „Erfolge der BCS-Theorie“, Unterabschnitt „Existenz einer Energielücke“, zweite Formel; wiederholt im Unterabschnitt „Isotopeneffekt“.

import Mathlib
import Definitions.Def_BCSTheory_GapEquation
open Filter Topology

namespace BCSTheory

theorem zeroTemperatureGap_eq (hbarOmegaD coupling : ℝ) (hω : 0 < hbarOmegaD)
    (hc : 0 < coupling) :
    (∀ Δ : ℝ, 0 < Δ →
      (gapIntegralZeroTemp hbarOmegaD Δ = 1 / coupling ↔
        Δ = hbarOmegaD / Real.sinh (1 / coupling))) ∧
    zeroTemperatureGap hbarOmegaD coupling = hbarOmegaD / Real.sinh (1 / coupling) := by sorry

end BCSTheory
