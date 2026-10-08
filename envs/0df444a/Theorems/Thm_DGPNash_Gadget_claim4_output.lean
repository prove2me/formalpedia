-- Prove2me | Theorems.Thm_DGPNash_Gadget_claim4_output
-- name    : DGPNash.Gadget.claim4_output
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T18:29:31.177254+00:00
-- url     : https://prove2.me/theorems/aeb09d5c-286b-4f25-9e32-d4133d6514ce
-- title:
--   Claim 4 — $p[v_3] = \min\{1, \alpha p[v_1] + \beta p[v_2] + \gamma p[v_1]p[v_2]\} \pm 81\epsilon$
-- statement:
--   Let $\alpha, \beta, \gamma$ be nonnegative integers with $\alpha + \beta + \gamma \le 3$, let $\epsilon \in [0, 0.01]$, and consider $\mathcal G_{+,*}$ with parameters $\alpha, \beta, \gamma$. Then at every $\epsilon$-Nash equilibrium of $\mathcal G_{+,*}$,
--   $$\Big|\,p[v_3] - \min\{1,\ \alpha p[v_1] + \beta p[v_2] + \gamma p[v_1]p[v_2]\}\Big| \le 81\,\epsilon .$$
--
--   Fourth and last claim in the proof of Proposition 4.18: the subgame on $v_2', w_3, v_3$ multiplies $p[v_2' : *]$ by $8$ and truncates at $1$. It is the arithmetic half of Proposition 4.18; the proposition adds that the game is legally 3-colorable.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), p. 232, Claim 4 (in the proof of Proposition 4.18)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_Gadget_EpsNash
import Definitions.Def_DGPNash_Gadget_AffectsGraph
import Definitions.Def_DGPNash_Gadget_AddMulGame

namespace DGPNash.Gadget

/-- Claim 4 (p. 232): at any ε-Nash equilibrium of `G_{+,∗}`,
`p[v₃] = min{1, α p[v₁] + β p[v₂] + γ p[v₁] p[v₂]} ± 81ε`. -/
theorem claim4_output (α β γ : ℕ) (hαβγ : α + β + γ ≤ 3) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 100) (σ : ∀ r, AddMulStrat r → ℝ) (hσ : IsEpsNash (addMulPayoff α β γ) ε σ) :
    |σ .v3 (1 : Fin 2) - min 1 ((α : ℝ) * σ .v1 (1 : Fin 2) + (β : ℝ) * σ .v2 (1 : Fin 2)
        + (γ : ℝ) * σ .v1 (1 : Fin 2) * σ .v2 (1 : Fin 2))| ≤ 81 * ε := by sorry

end DGPNash.Gadget
