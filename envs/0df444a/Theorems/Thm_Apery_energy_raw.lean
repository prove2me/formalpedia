-- Prove2me | Theorems.Thm_Apery_energy_raw
-- name    : Apery.energy_raw
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T00:16:04.599535+00:00
-- url     : https://prove2.me/theorems/447633eb-cbae-4cc0-bdd1-79bef425b834
-- title:
--   The raw configuration inequality with regularisation error
-- statement:
--   Let $n > 0$, $h = 37n$, $K = K_n = 40n$, let $\varepsilon > 0$, and let $t_1,\dots,t_h$ be pairwise distinct real numbers. With $U_\rho$ the potential of the comparison measure, $\mathrm{Err}$ the total regularisation error, and $I(\rho)$ the logarithmic energy of Appendix A,
--
--   $$\sum_{i,i'=1}^{h}\log|t_i - t_{i'}| \;\le\; -h\log\varepsilon \;+\; 2K\sum_{i=1}^{h}\bigl(U_\rho(t_i) + \mathrm{Err}(\varepsilon, t_i)\bigr) \;-\; K^2 I(\rho).$$
--
--   This is the raw configuration inequality of the source (`Apery/EnergyRaw.lean`), the starting point of the proof of the logarithmic-energy inequality (6.9): it is obtained by inserting the regularised pair potential on a circle, using Lemmas 6.1 and 6.2 (through the Arcsine/Gaussian kernel decomposition) and letting the circle radius tend to infinity. The dependence on the configuration is only through the one-point terms $U_\rho(t_i) + \mathrm{Err}(\varepsilon,t_i)$.
--
--   **Formalization Note** The statement uses the platform definitions `Definitions.Def_Zeta5_SourceEnergy` (for $U_\rho$, $\mathrm{Err}$), `Definitions.Def_Zeta5_SourceConstants` (for $K_n$) and `Definitions.Def_Zeta5_SourceMeasure` (for $I(\rho)$); the configuration is indexed by `Fin (37 * n)`.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/EnergyRaw.lean#L117-L124, the raw configuration inequality, proved from Apery/EnergyBlocks.lean and Apery/Kernel.lean

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceValue
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceMeasure
import Definitions.Def_Zeta5_SourceAnalytic
import Definitions.Def_Zeta5_SourceEnergy

open Polynomial Filter Topology Finset MeasureTheory

namespace Apery

theorem energy_raw (n : ℕ) (hn : 0 < n) (t : Fin (37 * n) → ℝ) (hinj : Function.Injective t)
    {ε : ℝ} (hε : 0 < ε) :
    ∑ i, ∑ i', Real.log |t i - t i'| ≤
      -(37 * n : ℝ) * Real.log ε + 2 * Kr n * ∑ i, (Uρ (t i) + Err ε (t i)) - Kr n ^ 2 * Irho := by sorry

end Apery
