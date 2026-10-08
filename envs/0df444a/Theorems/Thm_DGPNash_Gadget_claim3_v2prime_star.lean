-- Prove2me | Theorems.Thm_DGPNash_Gadget_claim3_v2prime_star
-- name    : DGPNash.Gadget.claim3_v2prime_star
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:29:21.505541+00:00
-- url     : https://prove2.me/theorems/df66664d-48b6-4160-9d41-cf22b2a71fd3
-- title:
--   Claim 3 — $p[v_2' : *] = \tfrac{\alpha}{8}p[v_1] + \tfrac{\beta}{8}p[v_2] + \tfrac{\gamma}{8}p[v_1]p[v_2] \pm 10\epsilon$
-- statement:
--   Let $\alpha, \beta, \gamma$ be nonnegative integers with $\alpha + \beta + \gamma \le 3$, let $\epsilon \in [0, 0.01]$, and consider $\mathcal G_{+,*}$ with parameters $\alpha, \beta, \gamma$. Then at every $\epsilon$-Nash equilibrium of $\mathcal G_{+,*}$, the probability $p[v_2' : *]$ that $v_2'$ plays $*$ satisfies
--   $$\Big|\,p[v_2' : *] - \Big(\frac{\alpha}{8}p[v_1] + \frac{\beta}{8}p[v_2] + \frac{\gamma}{8}p[v_1]p[v_2]\Big)\Big| \le 10\,\epsilon .$$
--
--   Third claim in the proof of Proposition 4.18: the players $w$ and $u$ make $v_2'$ divide its weight between $1$ and $*$ so that $*$ carries one eighth of the target arithmetic expression. The hypotheses $\alpha + \beta + \gamma \le 3$ and $\epsilon \le 0.01$ are where the claim needs them.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), p. 232, Claim 3 (in the proof of Proposition 4.18)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_Gadget_EpsNash
import Definitions.Def_DGPNash_Gadget_AffectsGraph
import Definitions.Def_DGPNash_Gadget_AddMulGame

namespace DGPNash.Gadget

/-- Claim 3 (p. 232): at any ε-Nash equilibrium of `G_{+,∗}`,
`p[v₂' : ∗] = (α/8) p[v₁] + (β/8) p[v₂] + (γ/8) p[v₁] p[v₂] ± 10ε`. -/
theorem claim3_v2prime_star (α β γ : ℕ) (hαβγ : α + β + γ ≤ 3) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 100) (σ : ∀ r, AddMulStrat r → ℝ) (hσ : IsEpsNash (addMulPayoff α β γ) ε σ) :
    |σ .v2' Tri.star - ((α : ℝ) / 8 * σ .v1 (1 : Fin 2) + (β : ℝ) / 8 * σ .v2 (1 : Fin 2)
        + (γ : ℝ) / 8 * σ .v1 (1 : Fin 2) * σ .v2 (1 : Fin 2))| ≤ 10 * ε := by sorry

end DGPNash.Gadget
