-- Prove2me | Theorems.Thm_BayesRouting_VOI_eqPotential_regime_monotone
-- name    : BayesRouting.VOI.eqPotential_regime_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T15:07:38.58756+00:00
-- url     : https://prove2.me/theorems/98c462d6-bcea-4d25-b1eb-9df5c5238c8c
-- title:
--   Proposition 3 — $\Psi$ strictly decreases in $\Lambda^{ij}_1$, is constant in $\Lambda^{ij}_2$, strictly increases in $\Lambda^{ij}_3$ along $z^{ij}$
-- statement:
--   Let $i\ne j$ be two populations, $\lambda$ in the simplex with $\lambda^i,\lambda^j>0$, and $\varepsilon>0$ such that $\lambda'=\lambda+\varepsilon z^{ij}$ still has $\lambda'^j>0$. Along $z^{ij}$ the vector $\lambda^{-ij}$, and hence the thresholds $\underline\lambda^i,\overline\lambda^i$, do not change. Then
--
--   1. if $\lambda,\lambda'\in\Lambda^{ij}_1$: $\Psi(\lambda')<\Psi(\lambda)$;
--   2. if $\lambda,\lambda'\in\Lambda^{ij}_2$: $\Psi(\lambda')=\Psi(\lambda)$;
--   3. if $\lambda,\lambda'\in\Lambda^{ij}_3$: $\Psi(\lambda')>\Psi(\lambda)$.
--
--   Furthermore, for every BWE $q$ of $\Gamma(\lambda)$, the equilibrium edge load $w^*(\lambda)$ equals the (common) edge load $w^{ij,\dagger}$ of the flows in $\mathcal F^{ij,\dagger}$ if and only if $\lambda\in\Lambda^{ij}_2$: in $\Lambda^{ij}_2$ it equals the edge load of every $f\in\mathcal F^{ij,\dagger}$, and if it equals the edge load of some $f\in\mathcal F^{ij,\dagger}$ then $\lambda\in\Lambda^{ij}_2$.
--
--   **Formalization Note** The paper says "monotonically decreases/increases"; the paragraph after the proposition says $\Psi$ strictly decreases (increases), and the proof of Theorem 3 needs the strict version, so the strict reading is stated. $w^{ij,\dagger}$ is not a separate object: the claim is phrased through the flows of $\mathcal F^{ij,\dagger}$ (whose edge load is unique under the full-support assumption). The regime conditions of $\lambda'$ use the thresholds of $\lambda$, which are equal to those of $\lambda'$ by definition.
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, p. 157, Proposition 3 (and the paragraph following it)

import Mathlib
import Definitions.Def_BayesRouting_VOI_Game
import Definitions.Def_BayesRouting_VOI_Potential
import Definitions.Def_BayesRouting_VOI_Flows
import Definitions.Def_BayesRouting_VOI_Pairwise

namespace BayesRouting.VOI

/-- **Proposition 3** (Wu, Amin, Ozdaglar, Oper. Res. 69(1) 2021, p. 157). Fix distinct populations
`i, j` and perturb an admissible `λ` to `λ + ε z^{ij}`, `ε > 0`, staying admissible. The thresholds
of `λ + ε z^{ij}` equal those of `λ` (both depend only on `λ^{-ij}`, which is unchanged), and:
`Ψ` strictly decreases when both endpoints are in `Λ^{ij}_1`, is unchanged when both are in
`Λ^{ij}_2`, and strictly increases when both are in `Λ^{ij}_3`. Moreover, for every BWE `q` of `Γ(λ)`,
the equilibrium edge load equals the edge load `w^{ij,†}` of the flows in `ℱ^{ij,†}` if and only if
`λ ∈ Λ^{ij}_2`. -/
theorem eqPotential_regime_monotone {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) (i j : I) (hij : i ≠ j) :
    (∀ lam ∈ stdSimplex ℝ I, 0 < lam i → 0 < lam j →
      ∀ ε : ℝ, 0 < ε → 0 < (lam + ε • dir i j) j →
        ((lam i < lowThr G lam i j ∧ (lam + ε • dir i j) i < lowThr G lam i j) →
            eqPotential G (lam + ε • dir i j) < eqPotential G lam) ∧
        ((lowThr G lam i j ≤ lam i ∧ lam i ≤ highThr G lam i j ∧
            lowThr G lam i j ≤ (lam + ε • dir i j) i ∧ (lam + ε • dir i j) i ≤ highThr G lam i j) →
            eqPotential G (lam + ε • dir i j) = eqPotential G lam) ∧
        ((highThr G lam i j < lam i ∧ highThr G lam i j < (lam + ε • dir i j) i) →
            eqPotential G lam < eqPotential G (lam + ε • dir i j))) ∧
    (∀ lam ∈ stdSimplex ℝ I, 0 < lam i → 0 < lam j →
      ∀ q : (k : I) → T k → R → ℝ, IsBWE G lam q →
        ((lowThr G lam i j ≤ lam i ∧ lam i ≤ highThr G lam i j) →
            ∀ f ∈ pairOptimal G lam i j, edgeLoad G q = flowLoad G f) ∧
        ((∃ f ∈ pairOptimal G lam i j, edgeLoad G q = flowLoad G f) →
            lowThr G lam i j ≤ lam i ∧ lam i ≤ highThr G lam i j)) := by sorry

end BayesRouting.VOI
