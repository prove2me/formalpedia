-- Prove2me | Theorems.Thm_ClausiusDuhem_local_of_integral
-- name    : ClausiusDuhem.local_of_integral
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:54.998197+00:00
-- url     : https://prove2.me/theorems/9cf88209-9002-43f0-bfdd-ff8591ba0a15
-- title:
--   Localization of the integral Clausius–Duhem inequality
-- statement:
--   Let $(\rho,\eta,\mathbf v,\mathbf q,s,T,e,\boldsymbol\sigma)$ be a thermomechanical process such that $\rho,\eta,\mathbf v,\mathbf q,T,e$ are $C^1$ jointly in $(t,x)$, $s$ is jointly continuous, and $T>0$ everywhere. Suppose that for every non-degenerate closed box $\Omega=[a,b]\subset\mathbb R^3$ (a fixed control volume) and every time $t$,
--   $$\frac{d}{dt}\int_\Omega\rho\eta\,dV\ge-\int_{\partial\Omega}\rho\eta\,\mathbf v\cdot\mathbf n\,dA-\int_{\partial\Omega}\frac{\mathbf q\cdot\mathbf n}{T}\,dA+\int_\Omega\frac{\rho s}{T}\,dV.$$
--   Then at every time $t$ and every point $x$,
--   $$\frac{\partial}{\partial t}(\rho\eta)\ge-\nabla\cdot(\rho\eta\,\mathbf v)-\nabla\cdot\Big(\frac{\mathbf q}{T}\Big)+\frac{\rho s}{T}.$$
--
--   This is the step from the integral (global) statement of the second law to a pointwise statement.
--
--   **Formalization Note** Boxes serve as control volumes; their boundary integrals are sums of face integrals with outward normals $\pm\mathbf e_i$.
-- source:
--   Wikipedia, "Clausius–Duhem inequality", revision oldid=1182390552, https://en.wikipedia.org/w/index.php?title=Clausius%E2%80%93Duhem_inequality&oldid=1182390552, section "Clausius–Duhem inequality in terms of the specific entropy", Proof, from "Assume that Ω is an arbitrary fixed control volume" to "Since Ω is arbitrary, we must have".

import Definitions.Def_ClausiusDuhem_thermo_process

namespace ClausiusDuhem
theorem local_of_integral (P : ThermoProcess) (hP : P.Smooth)
    (hT : ∀ t x, 0 < P.temp t x) (hInt : P.IntegralEntropyInequality) :
    ∀ t x, timeDeriv (fun τ y => P.rho τ y * P.eta τ y) t x ≥
      -div (fun y => (P.rho t y * P.eta t y) • P.vel t y) x
      - div (fun y => (P.temp t y)⁻¹ • P.heatFlux t y) x
      + P.rho t x * P.source t x / P.temp t x := by sorry
end ClausiusDuhem
