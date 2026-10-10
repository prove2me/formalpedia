-- Prove2me | Theorems.Thm_BCSTheory_gap_near_Tc_weak_coupling
-- name    : BCSTheory.gap_near_Tc_weak_coupling
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:57.704222+00:00
-- url     : https://prove2.me/theorems/67621f87-8893-4fe9-a465-a708a4ae6b0e
-- title:
--   Near $T_c$: $\Delta(T)/\Delta(0) \approx 1.74\sqrt{1-T/T_c}$
-- statement:
--   For fixed $k_B,\hbar\omega_D>0$: for every coupling $\lambda>0$ the limit $L(\lambda) = \lim_{T\to T_c^-} \Delta(T)^2/(1-T/T_c)$ exists, and in the weak-coupling limit $$\lim_{\lambda\to0^+}\frac{L(\lambda)}{\Delta(0)^2} = \frac{8e^{2\gamma}}{7\zeta(3)} = (1.7367\ldots)^2,$$ i.e. $\Delta(T)/\Delta(0)\approx 1.74\sqrt{1-T/T_c}$ for $T\approx T_c$.
-- source:
--   Wikipedia (de), Artikel „BCS-Theorie“ (PDF-Ausdruck vom 05.10.2026), Abschnitt „Erfolge der BCS-Theorie“, Unterabschnitt „Existenz einer Energielücke“, Formel $\Delta(T)/\Delta(0)\approx1{,}74\sqrt{1-T/T_c}$ für $T\approx T_c$.

import Mathlib
import Definitions.Def_BCSTheory_GapEquation
open Filter Topology

namespace BCSTheory

theorem gap_near_Tc_weak_coupling (kB hbarOmegaD : ℝ) (hkB : 0 < kB)
    (hω : 0 < hbarOmegaD) :
    ∃ L : ℝ → ℝ,
      (∀ coupling : ℝ, 0 < coupling →
        Tendsto (fun T : ℝ => gap kB hbarOmegaD coupling T ^ 2 /
            (1 - T / criticalTemperature kB hbarOmegaD coupling))
          (𝓝[<] (criticalTemperature kB hbarOmegaD coupling)) (𝓝 (L coupling))) ∧
      Tendsto (fun coupling : ℝ => L coupling / zeroTemperatureGap hbarOmegaD coupling ^ 2)
        (𝓝[>] 0)
        (𝓝 (8 * Real.exp (2 * Real.eulerMascheroniConstant) / (7 * (riemannZeta 3).re))) := by sorry

end BCSTheory
