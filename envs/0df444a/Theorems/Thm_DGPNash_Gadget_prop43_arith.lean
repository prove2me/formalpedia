-- Prove2me | Theorems.Thm_DGPNash_Gadget_prop43_arith
-- name    : DGPNash.Gadget.prop43_arith
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:52:07.306575+00:00
-- url     : https://prove2.me/theorems/85342506-868c-4b94-9568-d693e5713884
-- title:
--   Proposition 4.3 — $p[v_3] = \min(\alpha p[v_1] + \beta p[v_2] + \gamma p[v_1]p[v_2], 1) \pm \epsilon$
-- statement:
--   Let $\alpha, \beta, \gamma \ge 0$ be real numbers and consider the binary graphical game with players $v_1, v_2, w, v_3$ in which the payoff to $v_3$ is $[w = 1]$ when $v_3$ plays $0$ and $[w = 0]$ when it plays $1$; the payoff to $w$ is $[v_3 = 1]$ when $w$ plays $1$, and, when $w$ plays $0$, it is $0, \beta, \alpha, \alpha+\beta+\gamma$ according as $(v_1, v_2) = (0,0), (0,1), (1,0), (1,1)$; the payoffs of $v_1, v_2$ are unconstrained. Then for every $0 \le \epsilon < 1$, in every $\epsilon$-Nash equilibrium,
--   $$\big|\,p[v_3] - \min(\alpha p[v_1] + \beta p[v_2] + \gamma p[v_1]p[v_2],\ 1)\,\big| \le \epsilon .$$
--   In particular, in every Nash equilibrium $p[v_3] = \min(\alpha p[v_1] + \beta p[v_2] + \gamma p[v_1]p[v_2], 1)$.
--
--   With $(\alpha, \beta, \gamma) = (1, 1, 0)$ this is the addition gadget $\mathcal G_+$, with $(0, 0, 1)$ the multiplication gadget $\mathcal G_*$.
--
--   **Formalization Note** The inputs have payoff $0$; $\epsilon \ge 0$ is added to the paper's $\epsilon < 1$.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), pp. 215–216, Proposition 4.3

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_Gadget_EpsNash
import Definitions.Def_DGPNash_Gadget_AffectsGraph
import Definitions.Def_DGPNash_Gadget_AddMulGame
import Definitions.Def_DGPNash_Gadget_BasicGadgets

namespace DGPNash.Gadget

/-- Proposition 4.3 (pp. 215–216): in every ε-Nash equilibrium of the game with the payoffs of
Proposition 4.3, `ε < 1`, `p[v₃] = min(α p[v₁] + β p[v₂] + γ p[v₁] p[v₂], 1) ± ε`. -/
theorem prop43_arith (α β γ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε < 1) (σ : ArithRole → Fin 2 → ℝ)
    (hσ : IsEpsNash (S := fun _ => Fin 2) (arithPayoff α β γ) ε σ) :
    |σ .v3 1 - min (α * σ .v1 1 + β * σ .v2 1 + γ * σ .v1 1 * σ .v2 1) 1| ≤ ε := by sorry

end DGPNash.Gadget
