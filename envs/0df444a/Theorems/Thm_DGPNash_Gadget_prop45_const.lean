-- Prove2me | Theorems.Thm_DGPNash_Gadget_prop45_const
-- name    : DGPNash.Gadget.prop45_const
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:52:09.595994+00:00
-- url     : https://prove2.me/theorems/b3d500b7-8826-4308-b359-771430892639
-- title:
--   Proposition 4.5 — $\mathcal G_\alpha$: $p[v_1] = \min(\alpha, 1) \pm \epsilon$
-- statement:
--   Let $\alpha \ge 0$ be a real number and consider the binary graphical game $\mathcal G_\alpha$ with players $w, v_1$, where the payoff to $v_1$ is $[w = 1]$ when $v_1$ plays $0$ and $[w = 0]$ when it plays $1$, and the payoff to $w$ is $\alpha$ when $w$ plays $0$ and $[v_1 = 1]$ when it plays $1$. Then for every $0 \le \epsilon < 1$, in every $\epsilon$-Nash equilibrium,
--   $$\big|\,p[v_1] - \min(\alpha, 1)\,\big| \le \epsilon .$$
--   In particular, in every Nash equilibrium $p[v_1] = \min(\alpha, 1)$.
--
--   This gadget assigns a fixed value to a player; the paper states it without proof.
--
--   **Formalization Note** $\epsilon \ge 0$ is added to the paper's $\epsilon < 1$.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), p. 218, Proposition 4.5

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_Gadget_EpsNash
import Definitions.Def_DGPNash_Gadget_AffectsGraph
import Definitions.Def_DGPNash_Gadget_AddMulGame
import Definitions.Def_DGPNash_Gadget_BasicGadgets

namespace DGPNash.Gadget

/-- Proposition 4.5 (p. 218): in every ε-Nash equilibrium of `G_α` with `ε < 1`,
`p[v₁] = min(α, 1) ± ε`. -/
theorem prop45_const (α : ℝ) (hα : 0 ≤ α) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1)
    (σ : ConstRole → Fin 2 → ℝ) (hσ : IsEpsNash (S := fun _ => Fin 2) (constPayoff α) ε σ) :
    |σ .v1 1 - min α 1| ≤ ε := by sorry

end DGPNash.Gadget
