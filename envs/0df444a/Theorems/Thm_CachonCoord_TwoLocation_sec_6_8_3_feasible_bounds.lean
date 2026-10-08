-- Prove2me | Theorems.Thm_CachonCoord_TwoLocation_sec_6_8_3_feasible_bounds
-- name    : CachonCoord.TwoLocation.sec_6_8_3_feasible_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:54:34.908617+00:00
-- url     : https://prove2.me/theorems/a0598bef-73c5-4b27-ab1f-59a351d33154
-- title:
--   §6.8.3, pp. 79–80 — s_r(s_s) > ŝ_r > 0 with F_r(ŝ_r) = β_r/(h_r + β_r), and s_s(s_r) > 0
-- statement:
--   In the decentralized two-location base-stock game (no contracts), the retailer's cost is $\pi_r(s_r,s_s) = c_r(s_r,s_s)$ and the supplier's is $\pi_s(s_r,s_s) = h_sI_s(s_s) + c_s(s_r,s_s)$. Let $\hat s_r$ be the minimizer of the retailer's single-location cost $c_r(y)$, characterized by
--   $$F_r(\hat s_r) = \frac{\beta_r}{h_r + \beta_r}.$$
--   Then:
--   1. $\hat s_r > 0$;
--   2. for every $s_s$, every best response $s_r(s_s)$ of the retailer (every minimizer of $\pi_r(\cdot, s_s)$) satisfies $s_r(s_s) > \hat s_r$;
--   3. for every $s_r$, every best response $s_s(s_r)$ of the supplier (every minimizer of $\pi_s(s_r,\cdot)$) satisfies $s_s(s_r) > 0$.
--
--   With imperfect replenishment the retailer always stocks more than it would with perfectly reliable replenishment, and the supplier always holds some inventory. These bounds delimit the feasible strategy sets $s_r > \hat s_r$, $s_s > 0$ on which the uniqueness of the decentralized equilibrium is argued.
--
--   **Formalization Note** The page writes $F_r(\hat s_r) = \beta/(h_r + \beta)$. The minimizer of $c_r(y) = h_rI_r(y) + \beta_rB_r(y)$ satisfies $F_r(\hat s_r) = \beta_r/(h_r+\beta_r)$, and the page itself glosses $\hat s_r$ as "optimal for the retailer in the single location model", so the corrected ratio is stated. Best responses are arbitrary minimizers over $\mathbb R$; their existence is not asserted.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.8.3, pp. 79–80 (the sentences 'For the retailer it is not difficult to show that s_r(s_s) > ŝ_r > 0 …' through 'For the supplier, s_s(s_r) > 0 …')

import Mathlib
import Definitions.Def_CachonCoord_TwoLocation_Model

namespace CachonCoord.TwoLocation

/-- §6.8.3, pp. 79–80 (the paragraph bounding the feasible strategies of the decentralized
game). With `ŝ_r` the minimizer of the retailer's single-location cost `c_r(y)`, characterized by
`F_r(ŝ_r) = β_r/(h_r + β_r)` (the page prints `β/(h_r + β)`; corrected, see the
natural-language statement): `ŝ_r > 0`, every best response `s_r(s_s)` of the retailer satisfies
`s_r(s_s) > ŝ_r`, and every best response `s_s(s_r)` of the supplier satisfies `s_s(s_r) > 0`. -/
theorem sec_6_8_3_feasible_bounds (M : Model) (shat : ℝ)
    (hshat : M.FR shat = M.br / (M.hr + M.br)) :
    0 < shat ∧
    (∀ ss sr : ℝ, IsMinOn (fun x => M.piR x ss) Set.univ sr → shat < sr) ∧
    (∀ sr ss : ℝ, IsMinOn (fun y => M.piS sr y) Set.univ ss → 0 < ss) := by sorry

end CachonCoord.TwoLocation
