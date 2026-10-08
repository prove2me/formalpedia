-- Prove2me | Theorems.Thm_DGPNash_Gadget_claim1_v1prime
-- name    : DGPNash.Gadget.claim1_v1prime
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:28:57.322801+00:00
-- url     : https://prove2.me/theorems/67f5231d-9509-4c29-97c0-027a592e7bd5
-- title:
--   Claim 1 — $p[v_1'] = \tfrac18 p[v_1] \pm \epsilon$ in $\mathcal G_{+,*}$
-- statement:
--   Let $\alpha, \beta, \gamma$ be nonnegative integers with $\alpha + \beta + \gamma \le 3$, let $\epsilon \in [0, 0.01]$, and consider the addition/multiplication game $\mathcal G_{+,*}$ with parameters $\alpha, \beta, \gamma$. For a binary player $v$, $p[v]$ denotes the probability that $v$ plays $1$. Then at every $\epsilon$-Nash equilibrium of $\mathcal G_{+,*}$,
--   $$\Big|\,p[v_1'] - \tfrac18\, p[v_1]\,\Big| \le \epsilon .$$
--
--   This is the first of the four claims that make up the proof of Proposition 4.18: the subgame on $v_1, w_1, v_1'$ copies the input $v_1$, scaled by $1/8$, into $v_1'$.
--
--   **Formalization Note** The hypotheses on $\alpha, \beta, \gamma$ and $\epsilon$ are those of Proposition 4.18, under which the claim is stated. The input strategies are arbitrary (the inputs have payoff $0$ in the Lean game).
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), p. 231, Claim 1 (in the proof of Proposition 4.18)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_Gadget_EpsNash
import Definitions.Def_DGPNash_Gadget_AffectsGraph
import Definitions.Def_DGPNash_Gadget_AddMulGame

namespace DGPNash.Gadget

/-- Claim 1 (p. 231): at any ε-Nash equilibrium of `G_{+,∗}`, `p[v₁'] = p[v₁]/8 ± ε`. -/
theorem claim1_v1prime (α β γ : ℕ) (hαβγ : α + β + γ ≤ 3) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 100) (σ : ∀ r, AddMulStrat r → ℝ) (hσ : IsEpsNash (addMulPayoff α β γ) ε σ) :
    |σ .v1' (1 : Fin 2) - (1 / 8) * σ .v1 (1 : Fin 2)| ≤ ε := by sorry

end DGPNash.Gadget
