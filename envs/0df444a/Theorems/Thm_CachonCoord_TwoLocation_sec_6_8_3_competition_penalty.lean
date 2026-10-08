-- Prove2me | Theorems.Thm_CachonCoord_TwoLocation_sec_6_8_3_competition_penalty
-- name    : CachonCoord.TwoLocation.sec_6_8_3_competition_penalty
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:54:52.878713+00:00
-- url     : https://prove2.me/theorems/a836f552-38a1-4a27-aa25-b61c343a45fc
-- title:
--   §6.8.3, pp. 80–81 — retailer under-stocks for every s_s, s_r(s_s°) < s_r°, and the competition penalty is positive
-- statement:
--   In the decentralized two-location base-stock game:
--   1. for every supplier base stock $s_s$, every minimizer $a$ of the retailer's retail-level cost $c_r(\cdot, s_s)$ and every minimizer $b$ of the chain's retail-level cost $c(\cdot, s_s)$ satisfy $a < b$;
--   2. if $\{s_r^o, s_s^o\}$ minimizes the supply chain's cost $\Pi$, then every best response of the retailer to $s_s^o$ satisfies $s_r(s_s^o) < s_r^o$;
--   3. at every Nash equilibrium $\{s_r^*, s_s^*\}$ of the decentralized game, the **competition penalty** is positive:
--   $$\frac{\Pi(s_r^*, s_s^*) - \Pi(s_r^o, s_s^o)}{\Pi(s_r^o, s_s^o)} > 0 .$$
--
--   Decentralized operation is therefore always suboptimal in this model. This is the reason a coordinating contract is needed.
--
--   **Formalization Note** The page writes the arguments of $\Pi$ in the penalty in the order $(s_s, s_r)$; the formalization uses $\Pi(s_r, s_s)$ throughout. The penalty is stated with the page's ratio, so the claim includes $\Pi(s_r^o,s_s^o) > 0$ implicitly (the ratio would be $0$ if the denominator vanished). The result uses $\beta_s > 0$, a standing assumption of the section (footnote 35 notes that with $\beta_s = 0$ the optimum can be an equilibrium).
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.8.3, pp. 80–81 (competition penalty display; 'In fact, there always exists a positive competition penalty …' through 's_r(s_s°) < s_r°')

import Mathlib
import Definitions.Def_CachonCoord_TwoLocation_Model
import Definitions.Def_CachonCoord_TwoLocation_Game

namespace CachonCoord.TwoLocation

/-- §6.8.3, pp. 80–81 ("there always exists a positive competition penalty"). Without
contracts: (1) for every `s_s`, the retailer's optimal base stock (a minimizer of `c_r(·, s_s)`)
is strictly lower than the supply chain's (a minimizer of `c(·, s_s)`); (2) for an optimal pair
`{s_r°, s_s°}`, `s_r(s_s°) < s_r°`; (3) at every Nash equilibrium `{s_r*, s_s*}` of the
decentralized game the competition penalty `(Π(s*) − Π(s°))/Π(s°)` is positive. -/
theorem sec_6_8_3_competition_penalty (M : Model) :
    (∀ ss a b : ℝ, IsMinOn (fun x => M.cR2 x ss) Set.univ a →
      IsMinOn (fun x => M.c2 x ss) Set.univ b → a < b) ∧
    (∀ srOpt ssOpt : ℝ, IsMinOn (fun p : ℝ × ℝ => M.Pi p.1 p.2) Set.univ (srOpt, ssOpt) →
      ∀ a : ℝ, IsMinOn (fun x => M.piR x ssOpt) Set.univ a → a < srOpt) ∧
    (∀ srOpt ssOpt : ℝ, IsMinOn (fun p : ℝ × ℝ => M.Pi p.1 p.2) Set.univ (srOpt, ssOpt) →
      ∀ srN ssN : ℝ, IsNashMin M.piR M.piS srN ssN →
        0 < (M.Pi srN ssN - M.Pi srOpt ssOpt) / M.Pi srOpt ssOpt) := by sorry

end CachonCoord.TwoLocation
