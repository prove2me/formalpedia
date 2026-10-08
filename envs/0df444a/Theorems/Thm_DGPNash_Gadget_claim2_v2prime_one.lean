-- Prove2me | Theorems.Thm_DGPNash_Gadget_claim2_v2prime_one
-- name    : DGPNash.Gadget.claim2_v2prime_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:29:07.130124+00:00
-- url     : https://prove2.me/theorems/427aedaa-252d-4c96-b6da-28b0e09192d6
-- title:
--   Claim 2 — $p[v_2' : 1] = \tfrac18 p[v_2] \pm \epsilon$ in $\mathcal G_{+,*}$
-- statement:
--   Let $\alpha, \beta, \gamma$ be nonnegative integers with $\alpha + \beta + \gamma \le 3$, let $\epsilon \in [0, 0.01]$, and consider $\mathcal G_{+,*}$ with parameters $\alpha, \beta, \gamma$. Write $p[v_2' : 1]$ for the probability that the three-strategy player $v_2'$ plays $1$, and $p[v_2]$ for the probability that $v_2$ plays $1$. Then at every $\epsilon$-Nash equilibrium of $\mathcal G_{+,*}$,
--   $$\Big|\,p[v_2' : 1] - \tfrac18\, p[v_2]\,\Big| \le \epsilon .$$
--
--   Second claim in the proof of Proposition 4.18: the subgame on $v_2, w_2, v_2'$ stores $p[v_2]/8$ as the weight $v_2'$ puts on strategy $1$.
--
--   **Formalization Note** $v_2'$'s strategies $\{0, 1, *\}$ are `Tri.zero`, `Tri.one`, `Tri.star`; $p[v_2' : 1]$ is `σ v2' Tri.one`.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), p. 231, Claim 2 (in the proof of Proposition 4.18)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_Gadget_EpsNash
import Definitions.Def_DGPNash_Gadget_AffectsGraph
import Definitions.Def_DGPNash_Gadget_AddMulGame

namespace DGPNash.Gadget

/-- Claim 2 (p. 231): at any ε-Nash equilibrium of `G_{+,∗}`, `p[v₂' : 1] = p[v₂]/8 ± ε`. -/
theorem claim2_v2prime_one (α β γ : ℕ) (hαβγ : α + β + γ ≤ 3) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 100) (σ : ∀ r, AddMulStrat r → ℝ) (hσ : IsEpsNash (addMulPayoff α β γ) ε σ) :
    |σ .v2' Tri.one - (1 / 8) * σ .v2 (1 : Fin 2)| ≤ ε := by sorry

end DGPNash.Gadget
