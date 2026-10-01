-- Prove2me | Theorems.Thm_BayesRouting_VOI_weighted_potential
-- name    : BayesRouting.VOI.weighted_potential
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T14:50:07.454377+00:00
-- url     : https://prove2.me/theorems/1d3243d3-aa4c-429c-9915-2a7f373e7c4d
-- title:
--   Lemma 1 — $\Gamma(\lambda)$ is a weighted potential game with potential $\Phi$ and weights $\Pr(t^i)$
-- statement:
--   Consider a Bayesian routing game with weighted potential
--
--   $$\Phi(q)=\sum_{s}\sum_{e}\sum_{t}\pi(s,t)\int_0^{\sum_{r\ni e}\sum_{i}q^i_r(t^i)}c^s_e(z)\,dz .$$
--
--   Then $\Phi$ is continuously differentiable, every type probability $\Pr(t^i)$ is positive, and for every strategy profile $q$, population $i$, type $t^i$ and route $r$,
--
--   $$\frac{\partial\Phi(q)}{\partial q^i_r(t^i)}=\Pr(t^i)\,\mathbb E[c_r(q)\mid t^i].$$
--
--   That is, $\Gamma(\lambda)$ is a weighted potential game in the sense of Sandholm, with positive type-specific weights $\gamma(t^i)=\Pr(t^i)$. This identity is what links equilibria to minimizers of $\Phi$.
--
--   **Formalization Note** The partial derivative is stated as a `HasDerivAt` of $x\mapsto\Phi(q[(i,t^i,r)\mapsto x])$ at $x=q^i_r(t^i)$, for every $q$ in the whole coordinate space (not only on $\mathcal Q(\lambda)$). Positivity of $\Pr(t^i)$ uses the added full-support assumption on the prior.
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, p. 154, Lemma 1 (with definition (8), pp. 153-154)

import Mathlib
import Definitions.Def_BayesRouting_VOI_Game
import Definitions.Def_BayesRouting_VOI_Potential

namespace BayesRouting.VOI

/-- **Lemma 1** (Wu, Amin, Ozdaglar, Oper. Res. 69(1) 2021, p. 154). `Γ(λ)` is a weighted
potential game (8) with potential `Φ` (9) and weights `γ(t^i) = Pr(t^i)`: `Φ` is continuously
differentiable, every weight `Pr(t^i)` is positive, and for every strategy profile `q` the
partial derivative of `Φ` in the coordinate `q^i_r(t^i)` is `Pr(t^i) 𝔼[c_r(q) | t^i]`. -/
theorem weighted_potential {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [DecidableEq R] [Nonempty R]
    (G : Game I T S E R) :
    ContDiff ℝ 1 (potential G) ∧
      ∀ (i : I) (ti : T i), 0 < typeProb G i ti ∧
        ∀ (q : (k : I) → T k → R → ℝ) (r : R),
          HasDerivAt (fun x => potential G (setCoord q i ti r x))
            (typeProb G i ti * expCost G q i ti r) (q i ti r) := by sorry

end BayesRouting.VOI
