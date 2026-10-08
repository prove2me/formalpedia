-- Prove2me | Theorems.Thm_CachonCoord_TwoLocation_p84_best_response_decreasing
-- name    : CachonCoord.TwoLocation.p84_best_response_decreasing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:09:01.843212+00:00
-- url     : https://prove2.me/theorems/4713a972-bb27-4875-ab7e-861bed006239
-- title:
--   §6.8.4, p. 84 — under (39)–(41) the retailer's best response s_r(s_s) is decreasing; the supplier's marginal cost along it
-- statement:
--   Under the Cachon–Zipkin contracts with $\lambda \in (0,1]$ (and any value $s_s^o$ in (41)), let $s_r(s_s)$ denote a best response of the retailer, i.e. a minimizer of the contracted retailer cost $\pi_r(\cdot, s_s)$. Then:
--   1. $s_r(\cdot)$ is decreasing: if $s_s \le s_s'$ then $s_r(s_s') \le s_r(s_s)$, for any choice of best responses;
--   2. along the best response the supplier's marginal cost in its own base stock is
--   $$\frac{\partial \pi_s(s_r(s_s), s_s)}{\partial s_s} = F_s(s_s)\big(h_s - (1-\lambda)\,c'(s_r(s_s)) + t_B^s\big) - t_B^s,$$
--   where the derivative is taken in the second argument of $\pi_s$ with $s_r = s_r(s_s)$ held fixed.
--
--   These two facts drive the uniqueness of the coordinated equilibrium.
--
--   **Formalization Note** The page derives monotonicity from an implicit-function-theorem formula for $\partial s_r(s_s)/\partial s_s$, whose denominator prints $f_s(s_s)c''(s_r)$ where the structure of (35) gives $F_s(s_s)c''(s_r)$. Monotonicity is stated directly for arbitrary minimizers, without densities or second derivatives. The page's further sentence that "the supplier's marginal cost is increasing" is not stated. Read literally it fails when $1 - \lambda$ is large: for small $s_s > 0$ the bracket can be negative and the product then decreases. Only the displayed formula is formalized.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.8.4, p. 84 (the paragraph after (43): 'From the implicit function theorem, s_r(s_s) is decreasing …' and the display of ∂π_s(s_r(s_s), s_s)/∂s_s)

import Mathlib
import Definitions.Def_CachonCoord_TwoLocation_Model
import Definitions.Def_CachonCoord_TwoLocation_Contracts

namespace CachonCoord.TwoLocation

/-- §6.8.4, p. 84 (after (43)). Under the contracts (39)–(41) with `λ ∈ (0, 1]`, the retailer's
best response `s_r(s_s)` is decreasing in `s_s`, and along it the supplier's marginal cost is
`∂π_s(s_r(s_s), s_s)/∂s_s = F_s(s_s)(h_s − (1 − λ) c'(s_r(s_s)) + t_B^s) − t_B^s`
(the partial derivative in the supplier's own base stock, at `s_r = s_r(s_s)`). -/
theorem p84_best_response_decreasing (M : Model) (lam ssOpt : ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam ≤ 1) :
    (∀ b1 b2 a1 a2 : ℝ, b1 ≤ b2 →
      IsMinOn (fun x => M.czPiR lam ssOpt x b1) Set.univ a1 →
      IsMinOn (fun x => M.czPiR lam ssOpt x b2) Set.univ a2 → a2 ≤ a1) ∧
    (∀ a b : ℝ, IsMinOn (fun x => M.czPiR lam ssOpt x b) Set.univ a →
      HasDerivAt (fun y => M.czPiS lam ssOpt a y)
        (M.FS b * (M.hs - (1 - lam) * M.cDeriv a + M.tBs lam ssOpt) - M.tBs lam ssOpt) b) := by sorry

end CachonCoord.TwoLocation
