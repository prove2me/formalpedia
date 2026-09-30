-- Prove2me | Theorems.Thm_BayesRouting_VOI_equilibrium_regimes
-- name    : BayesRouting.VOI.equilibrium_regimes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T15:06:16.242836+00:00
-- url     : https://prove2.me/theorems/c4941246-71da-45df-9b69-bb451a542358
-- title:
--   Theorem 2 — equilibrium route flows in the three regimes $\Lambda^{ij}_1,\Lambda^{ij}_2,\Lambda^{ij}_3$
-- statement:
--   Let $i\ne j$ be two populations and $\lambda$ in the simplex with $\lambda^i,\lambda^j>0$.
--
--   1. If $\lambda\in\Lambda^{ij}_1$ ($\lambda^i<\underline\lambda^i$), then
--   $$\mathcal F^*(\lambda)=\operatorname{argmin}\big\{\widehat\Phi(f):\ \text{(14a), (14b), (14c), (IIC}_{ij}),\ \text{(IIC}_k)\ \forall k\ne j\big\},$$
--   and (IIC$_i$) is tight at every equilibrium flow: $\widehat J^i(f)=\lambda^iD$ for all $f\in\mathcal F^*(\lambda)$.
--   2. If $\lambda\in\Lambda^{ij}_3$ ($\lambda^i>\overline\lambda^i$), the same holds with (IIC$_k$) for all $k\ne i$, and (IIC$_j$) is tight: $\widehat J^j(f)=\lambda^jD$ for all $f\in\mathcal F^*(\lambda)$.
--   3. If $\lambda\in\Lambda^{ij}_2$ ($\underline\lambda^i\le\lambda^i\le\overline\lambda^i$), then $\mathcal F^*(\lambda)\subseteq\mathcal F^{ij,\dagger}$.
--
--   In a side regime the information of the minor population affects its entire demand; in the middle regime the impact of information on neither population is fully attained.
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, p. 157, Theorem 2, eq. (25)

import Mathlib
import Definitions.Def_BayesRouting_VOI_Game
import Definitions.Def_BayesRouting_VOI_Potential
import Definitions.Def_BayesRouting_VOI_Flows
import Definitions.Def_BayesRouting_VOI_Pairwise

namespace BayesRouting.VOI

/-- **Theorem 2** (Wu, Amin, Ozdaglar, Oper. Res. 69(1) 2021, p. 157). For two distinct populations
`i, j` and an admissible size vector `λ`:
* in regime `Λ^{ij}_1` (`λ^i < λ̲^i`), `ℱ*(λ)` is the set of minimizers of `Φ̂` subject to
  (14a)–(14c), (IIC_{ij}) and (IIC_k) for all `k ≠ j`, and (IIC_i) is tight at every equilibrium flow;
* in regime `Λ^{ij}_3` (`λ̄^i < λ^i`), the same with the roles of `i` and `j` exchanged in the
  constraints, and (IIC_j) is tight;
* in regime `Λ^{ij}_2` (`λ̲^i ≤ λ^i ≤ λ̄^i`), `ℱ*(λ) ⊆ ℱ^{ij,†}`. -/
theorem equilibrium_regimes {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) (i j : I) (hij : i ≠ j) (lam : I → ℝ) (hlam : lam ∈ stdSimplex ℝ I)
    (hi : 0 < lam i) (hj : 0 < lam j) :
    (lam i < lowThr G lam i j →
        eqFlows G lam = flowArgmin G (flowBase G ∩
          {f | impact G i f + impact G j f ≤ (1 - restSize lam i j) * G.D ∧
            ∀ k, k ≠ j → impact G k f ≤ lam k * G.D}) ∧
        ∀ f ∈ eqFlows G lam, impact G i f = lam i * G.D) ∧
      (highThr G lam i j < lam i →
        eqFlows G lam = flowArgmin G (flowBase G ∩
          {f | impact G i f + impact G j f ≤ (1 - restSize lam i j) * G.D ∧
            ∀ k, k ≠ i → impact G k f ≤ lam k * G.D}) ∧
        ∀ f ∈ eqFlows G lam, impact G j f = lam j * G.D) ∧
      (lowThr G lam i j ≤ lam i → lam i ≤ highThr G lam i j →
        eqFlows G lam ⊆ pairOptimal G lam i j) := by sorry

end BayesRouting.VOI
