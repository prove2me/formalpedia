-- Prove2me | Theorems.Thm_CachonCoord_TwoLocation_sec_6_8_4_coordination
-- name    : CachonCoord.TwoLocation.sec_6_8_4_coordination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:09:15.42998+00:00
-- url     : https://prove2.me/theorems/1ae69ecb-23b5-47e1-9646-36292328aae4
-- title:
--   §6.8.4, pp. 84–85 — with s_s° > 0 and λ ∈ (0, 1], the transfers (39)–(41) make {s_r°, s_s°} the unique Nash equilibrium
-- statement:
--   Consider the two-location base-stock model, and let $\{s_r^o, s_s^o\}$ minimize the supply chain's cost $\Pi(s_r,s_s)$ over $\mathbb R^2$ with $s_s^o > 0$. Let $\lambda \in (0,1]$ and let the supplier pay the retailer the linear transfer $t_I I_r(s_r,s_s) + t_B^r B_r(s_r,s_s) + t_B^s B_s(s_s)$ with
--   $$t_I = (1-\lambda)h_r, \qquad t_B^r = \beta_r - \lambda\beta, \qquad t_B^s = \lambda h_s \frac{F_s(s_s^o)}{1-F_s(s_s^o)}. \qquad (39)\text{–}(41)$$
--   Then:
--   1. for all $(s_r,s_s)$ the contracted costs are
--   $$\pi_r(s_r,s_s) = \lambda c(s_r,s_s) - t_B^sB_s(s_s), \qquad \pi_s(s_r,s_s) = (h_s+t_B^s)I_s(s_s) + (1-\lambda)c(s_r,s_s) + t_B^s(\mu_s - s_s);$$
--   2. $\{s_r^o, s_s^o\}$ is a Nash equilibrium of the contracted game;
--   3. it is the unique Nash equilibrium.
--
--   The linear transfers therefore coordinate the two-location supply chain: the optimal base stocks become the only equilibrium. The parameter $\lambda$ divides the retail-level costs between the firms.
--
--   **Formalization Note** Clause 1 states (42) with $\lambda c(s_r,s_s)$ where the page prints $\lambda\Pi(s_r,s_s)$; see the milestone on (42)–(43). The existence of an optimal pair is the page's standing assumption ("There exists a pair of base stock levels … that minimize the supply chain's cost", p. 77) and is a hypothesis. Only the page's first case $s_s^o > 0$ is stated; the case $s_s^o \le 0$, with multiple equilibria, is not. Strategies range over all of $\mathbb R$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.8.4, pp. 84–85 (Eqs. (39)–(43); 'so {s_r°, s_s°} is indeed a Nash equilibrium. In fact, it is the unique Nash equilibrium.'; p. 85 'Thus, there is a unique s_s that satisfies s_s(s_r(s_s)) = s_s, i.e., there is a unique Nash equilibrium.')

import Mathlib
import Definitions.Def_CachonCoord_TwoLocation_Model
import Definitions.Def_CachonCoord_TwoLocation_Contracts
import Definitions.Def_CachonCoord_TwoLocation_Game

namespace CachonCoord.TwoLocation

/-- §6.8.4, pp. 84–85, the coordination result for the Cachon–Zipkin linear transfers. Let
`{s_r°, s_s°}` minimize the supply chain's cost `Π` with `s_s° > 0`, and let `λ ∈ (0, 1]`. Under
the contracts (39) `t_I = (1 − λ)h_r`, (40) `t_B^r = β_r − λβ`,
(41) `t_B^s = λh_s F_s(s_s°)/(1 − F_s(s_s°))`:
1. (42)–(43): the retailer's cost is `λ c(s_r, s_s) − t_B^s B_s(s_s)` (printed `λΠ`; corrected) and
   the supplier's is `(h_s + t_B^s) I_s(s_s) + (1 − λ) c(s_r, s_s) + t_B^s (μ_s − s_s)`;
2. `{s_r°, s_s°}` is a Nash equilibrium of the contracted game;
3. it is the unique Nash equilibrium. -/
theorem sec_6_8_4_coordination (M : Model) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (srOpt ssOpt : ℝ)
    (hopt : IsMinOn (fun p : ℝ × ℝ => M.Pi p.1 p.2) Set.univ (srOpt, ssOpt))
    (hss : 0 < ssOpt) :
    (∀ sr ss : ℝ,
      M.czPiR lam ssOpt sr ss = lam * M.c2 sr ss - M.tBs lam ssOpt * M.BS ss ∧
      M.czPiS lam ssOpt sr ss = (M.hs + M.tBs lam ssOpt) * M.IS ss + (1 - lam) * M.c2 sr ss
        + M.tBs lam ssOpt * (M.muS - ss)) ∧
    IsNashMin (M.czPiR lam ssOpt) (M.czPiS lam ssOpt) srOpt ssOpt ∧
    (∀ sr ss : ℝ, IsNashMin (M.czPiR lam ssOpt) (M.czPiS lam ssOpt) sr ss →
      sr = srOpt ∧ ss = ssOpt) := by sorry

end CachonCoord.TwoLocation
