-- Prove2me | Theorems.Thm_BayesRouting_VOI_loadPotential_strictConvex
-- name    : BayesRouting.VOI.loadPotential_strictConvex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T14:52:27.68898+00:00
-- url     : https://prove2.me/theorems/2bcbfb87-6c85-4753-81bd-cb9e2cd40840
-- title:
--   Lemma 2 — the edge-load potential $\check\Phi$ is strictly convex (and $C^2$ for $C^1$ costs)
-- statement:
--   Let
--
--   $$\check\Phi(w)=\sum_{s}\sum_{e}\sum_{t}\pi(s,t)\int_0^{w_e(t)}c^s_e(z)\,dz$$
--
--   be the potential of a Bayesian routing game as a function of the edge load $w=(w_e(t))_{e\in\mathcal E,t\in\mathcal T}$. Then:
--
--   1. $\check\Phi$ is strictly convex on the whole space of edge loads;
--   2. if every cost $c^s_e$ is continuously differentiable, $\check\Phi$ is twice continuously differentiable.
--
--   Strict convexity is the source of the uniqueness of the equilibrium edge load.
--
--   **Formalization Note** The paper states "twice continuously differentiable" under costs that are only assumed differentiable; that claim needs $c^s_e\in C^1$, which is therefore an **added hypothesis** of the second clause. Strict convexity uses the added full-support assumption: a type profile with zero probability would contribute nothing to $\check\Phi$.
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, p. 154, Lemma 2

import Mathlib
import Definitions.Def_BayesRouting_VOI_Game
import Definitions.Def_BayesRouting_VOI_Potential

namespace BayesRouting.VOI

/-- **Lemma 2** (Wu, Amin, Ozdaglar, Oper. Res. 69(1) 2021, p. 154). The edge-load potential
`Φ̌(w)` (11) is strictly convex, and it is twice continuously differentiable when every cost
`c^s_e` is continuously differentiable (the `C^2` clause needs this added hypothesis: the paper
assumes only differentiable costs). -/
theorem loadPotential_strictConvex {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) :
    StrictConvexOn ℝ Set.univ (loadPotential G) ∧
      ((∀ s e, ContDiff ℝ 1 (G.cost s e)) → ContDiff ℝ 2 (loadPotential G)) := by sorry

end BayesRouting.VOI
