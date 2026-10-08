-- Prove2me | Theorems.Thm_CachonCoord_TwoLocation_eq_42_43
-- name    : CachonCoord.TwoLocation.eq_42_43
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:08:44.11649+00:00
-- url     : https://prove2.me/theorems/35fe7d86-ac5e-4e9f-8a25-b1e8fed8c043
-- title:
--   Eqs. (42)–(43), p. 84 — under (39)–(41), π_r = λc(s_r, s_s) − t_B^s B_s(s_s) and π_s = (h_s + t_B^s)I_s + (1 − λ)c + t_B^s(μ_s − s_s)
-- statement:
--   Under the Cachon–Zipkin contracts $t_I = (1-\lambda)h_r$, $t_B^r = \beta_r - \lambda\beta$, $t_B^s = \lambda h_s F_s(s_s^o)/(1-F_s(s_s^o))$, the firms' costs (each firm's own cost after the linear transfer) satisfy, for all base stocks $(s_r, s_s)$,
--   $$\pi_r(s_r,s_s) = \lambda\, c(s_r,s_s) - t_B^s B_s(s_s), \qquad (42)$$
--   $$\pi_s(s_r,s_s) = (h_s + t_B^s)\,I_s(s_s) + (1-\lambda)\,c(s_r,s_s) + t_B^s(\mu_s - s_s). \qquad (43)$$
--
--   The contracts give the retailer the fraction $\lambda$ of the chain's retail-level cost and the supplier the rest, plus a supplier-backorder term. This makes the retailer's incentives proportional to the chain's in $s_r$.
--
--   **Formalization Note** The page prints (42) as $\lambda\Pi(s_r,s_s) - t_B^sB_s(s_s)$. The line above it on the page, $c_r(y) = \lambda c(y) - t_B^sB_s(s_s)$, gives $\lambda c(s_r,s_s)$, and $\Pi$ contains the extra term $h_sI_s(s_s)$, so the corrected identity with $c$ is stated. The difference $\lambda h_s I_s(s_s)$ does not depend on $s_r$ and so does not affect the retailer's best responses. The identities hold for every real $\lambda$ and every value of $s_s^o$ in (41); no range restriction is needed.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.8.4, p. 84, Eqs. (42) and (43) with the preceding display of the adjusted c_r(y)

import Mathlib
import Definitions.Def_CachonCoord_TwoLocation_Model
import Definitions.Def_CachonCoord_TwoLocation_Contracts

namespace CachonCoord.TwoLocation

/-- §6.8.4, p. 84, Eqs. (42)–(43). Under the contracts (39)–(41) with parameter `λ` (any
`λ` and any value `s_s°` used in (41)), for all base stocks `(s_r, s_s)` the retailer's cost is
`λ c(s_r, s_s) − t_B^s B_s(s_s)` (the page prints `λΠ(s_r, s_s)` in (42); corrected) and the
supplier's cost is `(h_s + t_B^s) I_s(s_s) + (1 − λ) c(s_r, s_s) + t_B^s (μ_s − s_s)`. -/
theorem eq_42_43 (M : Model) (lam ssOpt : ℝ) :
    ∀ sr ss : ℝ,
      M.czPiR lam ssOpt sr ss = lam * M.c2 sr ss - M.tBs lam ssOpt * M.BS ss ∧
      M.czPiS lam ssOpt sr ss = (M.hs + M.tBs lam ssOpt) * M.IS ss + (1 - lam) * M.c2 sr ss
        + M.tBs lam ssOpt * (M.muS - ss) := by sorry

end CachonCoord.TwoLocation
