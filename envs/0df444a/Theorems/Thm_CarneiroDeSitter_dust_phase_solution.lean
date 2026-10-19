-- Prove2me | Theorems.Thm_CarneiroDeSitter_dust_phase_solution
-- name    : CarneiroDeSitter.dust_phase_solution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T02:18:23.581636+00:00
-- url     : https://prove2.me/theorems/2921f328-aa39-4d8b-bd54-8b1271489351
-- title:
--   Eq. (14): $a=C(e^{\sigma t/2}-1)^{2/3}$ solves the dust phase with $\Lambda=\sigma H$
-- statement:
--   Let $C>0$, $\sigma>0$, let $a(t)=C(e^{\sigma t/2}-1)^{2/3}$ be the scale factor (14), and let $H=\dot a/a$ be its Hubble parameter. With the Friedmann equation $\rho_T=3H^2$, the late-time vacuum term $\Lambda=\sigma H$ and dust ($p_m=0$, so $p_T=-\Lambda$), the conservation equation (3) holds at every time $t>0$:
--   $$
--   \frac{d}{dt}\big(3H^2\big)+3H\big(3H^2-\sigma H\big)=0 .
--   $$
--
--   So (14) is a solution of the late-time dust era of the model, with $C$ an integration constant.
-- source:
--   S. Carneiro, "From de Sitter to de Sitter: a non-singular inflationary universe driven by vacuum", Int. J. Mod. Phys. D 15 (2006) 2241-2247, https://doi.org/10.1142/S0218271806009510, p. 2245, Eq. (14) and the preceding sentences

import Mathlib
import Definitions.Def_CarneiroDeSitter2006

open Real Filter Topology Asymptotics MeasureTheory Set

namespace CarneiroDeSitter

theorem dust_phase_solution (C σ : ℝ) (hC : 0 < C) (hσ : 0 < σ) (t : ℝ) (ht : 0 < t) :
    let H := fun s => deriv (dustScaleFactor C σ) s / dustScaleFactor C σ s
    deriv (fun s => 3 * H s ^ 2) t + 3 * H t * (3 * H t ^ 2 + (0 - σ * H t)) = 0 := by sorry

end CarneiroDeSitter
