-- Prove2me | Theorems.Thm_ClausiusDuhem_dissipation_inequality
-- name    : ClausiusDuhem.dissipation_inequality
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:37:33.965634+00:00
-- url     : https://prove2.me/theorems/87a62aaa-5bfb-4441-8643-db7e0b2b5123
-- title:
--   Clausius–Duhem (dissipation) inequality from the integral second law
-- statement:
--   Let $(\rho,\eta,\mathbf v,\mathbf q,s,T,e,\boldsymbol\sigma)$ be a thermomechanical process on $\mathbb R^3$: mass density, specific entropy, velocity, heat flux, energy source per unit mass, absolute temperature, specific internal energy and Cauchy stress. Assume
--
--   1. $\rho,\eta,\mathbf v,\mathbf q,T,e$ are $C^1$ jointly in $(t,x)$ and $s$ is jointly continuous;
--   2. $T>0$ everywhere;
--   3. the integral Clausius–Duhem inequality holds on every fixed control volume $\Omega$ (every non-degenerate closed box):
--   $$\frac{d}{dt}\int_\Omega\rho\eta\,dV\ge-\int_{\partial\Omega}\rho\eta\,\mathbf v\cdot\mathbf n\,dA-\int_{\partial\Omega}\frac{\mathbf q\cdot\mathbf n}{T}\,dA+\int_\Omega\frac{\rho s}{T}\,dV;$$
--   4. conservation of mass $\dot\rho+\rho\,\nabla\cdot\mathbf v=0$;
--   5. balance of energy $\rho\dot e-\boldsymbol\sigma:\nabla\mathbf v+\nabla\cdot\mathbf q-\rho s=0$.
--
--   Then the dissipation is nonnegative at every time and every point:
--   $$\mathcal D=\rho\,(T\dot\eta-\dot e)+\boldsymbol\sigma:\nabla\mathbf v-\frac{\mathbf q\cdot\nabla T}{T}\ge0.$$
--
--   This combines the article's three results: the integral second law implies the differential (entropy) form, which together with the balance of energy gives the internal-energy form, equivalently the dissipation inequality.
--
--   **Formalization Note** Control volumes are the non-degenerate closed boxes with fixed boundary ($u_n=0$).
-- source:
--   Wikipedia, "Clausius–Duhem inequality", revision oldid=1182390552, https://en.wikipedia.org/w/index.php?title=Clausius%E2%80%93Duhem_inequality&oldid=1182390552, all sections: integral form (fixed control volume), differential form, internal-energy form, and "Dissipation".

import Definitions.Def_ClausiusDuhem_thermo_process

namespace ClausiusDuhem
theorem dissipation_inequality (P : ThermoProcess) (hP : P.Smooth)
    (hT : ∀ t x, 0 < P.temp t x) (hInt : P.IntegralEntropyInequality)
    (hMass : P.MassConservation) (hEnergy : P.EnergyBalance) :
    ∀ t x, 0 ≤ P.dissipation t x := by sorry
end ClausiusDuhem
