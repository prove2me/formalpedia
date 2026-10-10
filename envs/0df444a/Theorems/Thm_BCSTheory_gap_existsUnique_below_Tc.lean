-- Prove2me | Theorems.Thm_BCSTheory_gap_existsUnique_below_Tc
-- name    : BCSTheory.gap_existsUnique_below_Tc
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:07.650315+00:00
-- url     : https://prove2.me/theorems/b7d03e6d-625a-4da8-9803-9656906a5bc0
-- title:
--   For $0<T<T_c$ the gap equation has a unique positive solution; none for $T\ge T_c$
-- statement:
--   For $k_B,\hbar\omega_D,\lambda>0$: for every $0<T<T_c$ the finite-temperature gap equation $\frac1\lambda = \int_0^{\hbar\omega_D}\frac{d\eta}{\sqrt{\eta^2+\Delta^2}}\tanh\frac{\sqrt{\eta^2+\Delta^2}}{2k_BT}$ has exactly one solution $\Delta>0$ (namely $\Delta(T)$), and for every $T\ge T_c$ it has no solution $\Delta>0$ (the gap vanishes).
-- source:
--   Wikipedia (de), Artikel „BCS-Theorie“ (PDF-Ausdruck vom 05.10.2026), Abschnitt „Erfolge der BCS-Theorie“, Unterabschnitt „Existenz einer Energielücke“ ($\Delta(T)$ als implizite Lösung; $\Delta(T_c)=0$).

import Mathlib
import Definitions.Def_BCSTheory_GapEquation
open Filter Topology

namespace BCSTheory

theorem gap_existsUnique_below_Tc (kB hbarOmegaD coupling : ℝ) (hkB : 0 < kB)
    (hω : 0 < hbarOmegaD) (hc : 0 < coupling) :
    (∀ T : ℝ, 0 < T → T < criticalTemperature kB hbarOmegaD coupling →
      ∃! Δ : ℝ, 0 < Δ ∧ gapIntegral kB hbarOmegaD Δ T = 1 / coupling) ∧
    (∀ T : ℝ, criticalTemperature kB hbarOmegaD coupling ≤ T →
      ¬ ∃ Δ : ℝ, 0 < Δ ∧ gapIntegral kB hbarOmegaD Δ T = 1 / coupling) := by sorry

end BCSTheory
