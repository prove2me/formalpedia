-- Prove2me | Theorems.Thm_BCSTheory_criticalTemperature_isotope_effect
-- name    : BCSTheory.criticalTemperature_isotope_effect
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:16.832012+00:00
-- url     : https://prove2.me/theorems/d83d202b-e3aa-45f0-acba-41e11ccda602
-- title:
--   Isotope effect: $T_c \propto M^{-1/2}$ when $\omega_D \propto M^{-1/2}$
-- statement:
--   Let $k_B>0$, $\lambda=V_0Z(E_F)>0$, $C>0$ and an ionic mass $M>0$. If the Debye energy is $\hbar\omega_D = C/\sqrt{M}$, then $$T_c\bigl(C/\sqrt M\bigr) = T_c(C)\cdot M^{-1/2},$$ i.e. $T_c \propto M^{-\alpha}$ with $\alpha = 1/2$.
-- source:
--   Wikipedia (de), Artikel „BCS-Theorie“ (PDF-Ausdruck vom 05.10.2026), Abschnitt „Erfolge der BCS-Theorie“, Unterabschnitt „Isotopeneffekt“ ($T_c\propto M^{-\alpha}$, $\alpha\approx0{,}5$, mit $\omega_D \propto 1/\sqrt M$).

import Mathlib
import Definitions.Def_BCSTheory_GapEquation
open Filter Topology

namespace BCSTheory

theorem criticalTemperature_isotope_effect (kB C coupling M : ℝ) (hkB : 0 < kB)
    (hC : 0 < C) (hc : 0 < coupling) (hM : 0 < M) :
    criticalTemperature kB (C / Real.sqrt M) coupling =
      criticalTemperature kB C coupling * M ^ (-(1 / 2 : ℝ)) := by sorry

end BCSTheory
