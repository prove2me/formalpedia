-- Prove2me | Theorems.Thm_Apery_pairInt_log_symm
-- name    : Apery.pairInt_log_symm
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T00:34:37.39549+00:00
-- url     : https://prove2.me/theorems/8a583fc7-9e90-4dcd-a51b-bb1934d631e9
-- title:
--   Symmetry of the logarithmic pair integrals
-- statement:
--   For a configuration $t$, $\varepsilon > 0$ and two atom indices $k, l$, the pair integral of the logarithmic kernel is symmetric in the two atoms:
--
--   $$\int_0^{2\pi}\!\!\int_0^{2\pi} \log\|\gamma_k(\theta) - \gamma_l(\varphi)\|\,d\varphi\,d\theta \;=\; \int_0^{2\pi}\!\!\int_0^{2\pi} \log\|\gamma_l(\theta) - \gamma_k(\varphi)\|\,d\varphi\,d\theta .$$
--
--   This is the symmetry lemma of `Apery/EnergyAtoms.lean`, used to reorder the arcsine–arcsine blocks in the proof of the raw configuration inequality `energy_raw`.
--
--   **Formalization Note** The statement uses `Definitions.Def_Zeta5_SourceAtoms` (for `pairInt`, `atomγ`, `Idx`).
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/EnergyAtoms.lean#L260-L265, symmetry of the pair integrals

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceValue
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceMeasure
import Definitions.Def_Zeta5_SourceAnalytic
import Definitions.Def_Zeta5_SourceEnergy
import Definitions.Def_Zeta5_SourceAtoms

open Polynomial Filter Topology Finset MeasureTheory

namespace Apery

lemma pairInt_log_symm {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (k l : Idx h) :
    pairInt (atomγ t ε) (fun z w => Real.log ‖z - w‖) k l =
      pairInt (atomγ t ε) (fun z w => Real.log ‖z - w‖) l k := by sorry

end Apery
