-- Prove2me | Theorems.Thm_DGPNash_Gadget_addMulGadget_error_amplification
-- name    : DGPNash.Gadget.addMulGadget_error_amplification
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:29:44.026984+00:00
-- url     : https://prove2.me/theorems/ed29c095-a678-45f2-b50a-429f147e1b1d
-- title:
--   Proposition 4.18 — $\mathcal G_{+,*}$ is legally 3-colorable and has error amplification 81
-- statement:
--   Let $\alpha, \beta, \gamma$ be nonnegative integers such that $\alpha + \beta + \gamma \le 3$, and let $\mathcal G_{+,*}$ be the addition/multiplication game with input players $v_1, v_2$, output player $v_3$ and intermediate players $w_1, v_1', w_2, v_2', w_3, w, u$ (Fig. 11 and the payoff tables of the proof). Then:
--   1. the affects graph of $\mathcal G_{+,*}$ can be legally colored using three colors (Definition 4.8); and
--   2. for every $\epsilon \in [0, 0.01]$, at every $\epsilon$-Nash equilibrium of $\mathcal G_{+,*}$,
--   $$\Big|\,p[v_3] - \min\{1,\ \alpha p[v_1] + \beta p[v_2] + \gamma p[v_1]p[v_2]\}\Big| \le 81\,\epsilon ;$$
--   in particular, at every Nash equilibrium $p[v_3] = \min\{1, \alpha p[v_1] + \beta p[v_2] + \gamma p[v_1]p[v_2]\}$.
--
--   This is the gadget with which the paper reduces $r$-player games to three-player games: unlike the separate addition and multiplication gadgets, it can be glued into a larger graphical game so that the whole game stays legally 3-colorable, and each color class becomes one player of a three-player normal-form game.
--
--   **Formalization Note** The paper says "there is a graphical game $\mathcal G_{+,*}$"; the statement is made for the explicit game of its proof, with the input players' payoffs set to $0$ so that their mixed strategies are arbitrary. The affects graph is computed from the payoff functions. The "in particular" clause is the case $\epsilon = 0$.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), p. 230, Proposition 4.18 (proof pp. 230–233, Fig. 11)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_Gadget_EpsNash
import Definitions.Def_DGPNash_Gadget_AffectsGraph
import Definitions.Def_DGPNash_Gadget_AddMulGame

namespace DGPNash.Gadget

/-- Proposition 4.18 (p. 230): for nonnegative integers `α, β, γ` with `α + β + γ ≤ 3`, the game
`G_{+,∗}` (i) can be legally colored with three colors and (ii) at every ε-Nash equilibrium with
`ε ∈ [0, 0.01]` satisfies `p[v₃] = min{1, α p[v₁] + β p[v₂] + γ p[v₁] p[v₂]} ± 81ε`. -/
theorem addMulGadget_error_amplification (α β γ : ℕ) (hαβγ : α + β + γ ≤ 3) :
    IsLegallyColorable (addMulPayoff α β γ) 3 ∧
    ∀ (ε : ℝ), 0 ≤ ε → ε ≤ 1 / 100 → ∀ σ : ∀ r, AddMulStrat r → ℝ,
      IsEpsNash (addMulPayoff α β γ) ε σ →
      |σ .v3 (1 : Fin 2) - min 1 ((α : ℝ) * σ .v1 (1 : Fin 2) + (β : ℝ) * σ .v2 (1 : Fin 2)
        + (γ : ℝ) * σ .v1 (1 : Fin 2) * σ .v2 (1 : Fin 2))| ≤ 81 * ε := by sorry

end DGPNash.Gadget
