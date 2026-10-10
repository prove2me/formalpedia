-- Prove2me | Theorems.Thm_ClausiusDuhem_entropy_inequality_of_local
-- name    : ClausiusDuhem.entropy_inequality_of_local
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:35:42.816977+00:00
-- url     : https://prove2.me/theorems/d2160234-18e6-4c16-b124-9c23132bbd6a
-- title:
--   Differential form $\rho\dot\eta\ge-\nabla\cdot(\mathbf q/T)+\rho s/T$
-- statement:
--   Let $(\rho,\eta,\mathbf v,\mathbf q,s,T,e,\boldsymbol\sigma)$ be a thermomechanical process with $\rho,\eta,\mathbf v,\mathbf q,T,e$ jointly $C^1$ and $s$ jointly continuous. Assume that at every time and point
--   $$\frac{\partial}{\partial t}(\rho\eta)\ge-\nabla\cdot(\rho\eta\,\mathbf v)-\nabla\cdot\Big(\frac{\mathbf q}{T}\Big)+\frac{\rho s}{T},$$
--   and that mass is conserved, $\dot\rho+\rho\,\nabla\cdot\mathbf v=0$. Then at every time and point
--   $$\rho\,\dot\eta\ge-\nabla\cdot\Big(\frac{\mathbf q}{T}\Big)+\frac{\rho s}{T}.$$
--
--   This is the Clausius–Duhem inequality in differential form, expressed with the specific entropy.
-- source:
--   Wikipedia, "Clausius–Duhem inequality", revision oldid=1182390552, https://en.wikipedia.org/w/index.php?title=Clausius%E2%80%93Duhem_inequality&oldid=1182390552, section "Clausius–Duhem inequality in terms of the specific entropy", differential form and Proof, from "Expanding out" to the final display.

import Definitions.Def_ClausiusDuhem_thermo_process

namespace ClausiusDuhem
theorem entropy_inequality_of_local (P : ThermoProcess) (hP : P.Smooth)
    (hLocal : ∀ t x, timeDeriv (fun τ y => P.rho τ y * P.eta τ y) t x ≥
      -div (fun y => (P.rho t y * P.eta t y) • P.vel t y) x
      - div (fun y => (P.temp t y)⁻¹ • P.heatFlux t y) x
      + P.rho t x * P.source t x / P.temp t x)
    (hMass : P.MassConservation) :
    P.EntropyInequality := by sorry
end ClausiusDuhem
