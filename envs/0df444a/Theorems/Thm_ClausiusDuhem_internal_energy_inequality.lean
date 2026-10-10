-- Prove2me | Theorems.Thm_ClausiusDuhem_internal_energy_inequality
-- name    : ClausiusDuhem.internal_energy_inequality
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:36:23.944359+00:00
-- url     : https://prove2.me/theorems/025198cf-aa9a-40e0-8f5f-4e6101f0837d
-- title:
--   Clausius–Duhem inequality in terms of specific internal energy
-- statement:
--   Let $(\rho,\eta,\mathbf v,\mathbf q,s,T,e,\boldsymbol\sigma)$ be a thermomechanical process with $\rho,\eta,\mathbf v,\mathbf q,T,e$ jointly $C^1$, $s$ jointly continuous and absolute temperature $T>0$ everywhere. Assume the differential Clausius–Duhem inequality $\rho\dot\eta\ge-\nabla\cdot(\mathbf q/T)+\rho s/T$ and the balance of energy
--   $$\rho\dot e-\boldsymbol\sigma:\nabla\mathbf v+\nabla\cdot\mathbf q-\rho s=0$$
--   at every time and point. Then at every time and point
--   $$\rho\,(\dot e-T\dot\eta)-\boldsymbol\sigma:\nabla\mathbf v\le-\frac{\mathbf q\cdot\nabla T}{T}.$$
--
--   This form incorporates the balance of energy into the Clausius–Duhem inequality and is the form used to restrict constitutive relations.
-- source:
--   Wikipedia, "Clausius–Duhem inequality", revision oldid=1182390552, https://en.wikipedia.org/w/index.php?title=Clausius%E2%80%93Duhem_inequality&oldid=1182390552, section "Clausius–Duhem inequality in terms of specific internal energy" (statement and Proof).

import Definitions.Def_ClausiusDuhem_thermo_process

namespace ClausiusDuhem
theorem internal_energy_inequality (P : ThermoProcess) (hP : P.Smooth)
    (hT : ∀ t x, 0 < P.temp t x) (hEntropy : P.EntropyInequality)
    (hEnergy : P.EnergyBalance) :
    P.InternalEnergyInequality := by sorry
end ClausiusDuhem
