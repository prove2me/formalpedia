-- Prove2me | Theorems.Thm_DGPNash_Gadget_prop42_mul
-- name    : DGPNash.Gadget.prop42_mul
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:51:56.706981+00:00
-- url     : https://prove2.me/theorems/b9d6bebb-efd1-4516-9bc0-e2a3d1fb82ff
-- title:
--   Proposition 4.2 — $\mathcal G_{\times\alpha}$: $p[v_2] = \min(\alpha p[v_1], 1) \pm \epsilon$
-- statement:
--   Let $\alpha \ge 0$ be a real number and consider the binary graphical game $\mathcal G_{\times\alpha}$ with players $v_1, w, v_2$ in which the payoff to $v_2$ is $[w = 1]$ when $v_2$ plays $0$ and $[w = 0]$ when $v_2$ plays $1$, and the payoff to $w$ is $\alpha[v_1 = 1]$ when $w$ plays $0$ and $[v_2 = 1]$ when $w$ plays $1$; the payoff of $v_1$ is unconstrained. Then for every $\epsilon$ with $0 \le \epsilon < 1$, in every $\epsilon$-Nash equilibrium,
--   $$\big|\,p[v_2] - \min(\alpha\, p[v_1], 1)\,\big| \le \epsilon .$$
--   In particular ($\epsilon = 0$), in every Nash equilibrium $p[v_2] = \min(\alpha p[v_1], 1)$.
--
--   This is the scaling gadget; with $\alpha = 1$ it is the copy gadget $\mathcal G_=$.
--
--   **Formalization Note** The input $v_1$ has payoff $0$, so its mixed strategy is arbitrary at an $\epsilon$-Nash equilibrium. The paper's range "$\epsilon < 1$" is taken together with $\epsilon \ge 0$, since $\epsilon$ is a tolerance.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), p. 215, Proposition 4.2

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_Gadget_EpsNash
import Definitions.Def_DGPNash_Gadget_AffectsGraph
import Definitions.Def_DGPNash_Gadget_AddMulGame
import Definitions.Def_DGPNash_Gadget_BasicGadgets

namespace DGPNash.Gadget

/-- Proposition 4.2 (p. 215): in every ε-Nash equilibrium of `G_{×α}` with `ε < 1`,
`p[v₂] = min(α p[v₁], 1) ± ε`. -/
theorem prop42_mul (α : ℝ) (hα : 0 ≤ α) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1)
    (σ : MulRole → Fin 2 → ℝ) (hσ : IsEpsNash (S := fun _ => Fin 2) (mulPayoff α) ε σ) :
    |σ .v2 1 - min (α * σ .v1 1) 1| ≤ ε := by sorry

end DGPNash.Gadget
