-- Prove2me | Theorems.Thm_ClausiusDuhem_dissipation_nonneg_iff
-- name    : ClausiusDuhem.dissipation_nonneg_iff
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:37:09.868998+00:00
-- url     : https://prove2.me/theorems/309de149-d7e6-4e8d-a05d-97c664c598d9
-- title:
--   $\mathcal D\ge0$ is the internal-energy Clausius–Duhem inequality
-- statement:
--   For any thermomechanical process, define the dissipation
--   $$\mathcal D=\rho\,(T\dot\eta-\dot e)+\boldsymbol\sigma:\nabla\mathbf v-\frac{\mathbf q\cdot\nabla T}{T}.$$
--   Then $\mathcal D\ge0$ at every time and point if and only if, at every time and point,
--   $$\rho\,(\dot e-T\dot\eta)-\boldsymbol\sigma:\nabla\mathbf v\le-\frac{\mathbf q\cdot\nabla T}{T}.$$
--
--   This is why the Clausius–Duhem inequality is also called the dissipation inequality.
-- source:
--   Wikipedia, "Clausius–Duhem inequality", revision oldid=1182390552, https://en.wikipedia.org/w/index.php?title=Clausius%E2%80%93Duhem_inequality&oldid=1182390552, section "Dissipation".

import Definitions.Def_ClausiusDuhem_thermo_process

namespace ClausiusDuhem
theorem dissipation_nonneg_iff (P : ThermoProcess) :
    (∀ t x, 0 ≤ P.dissipation t x) ↔ P.InternalEnergyInequality := by sorry
end ClausiusDuhem
