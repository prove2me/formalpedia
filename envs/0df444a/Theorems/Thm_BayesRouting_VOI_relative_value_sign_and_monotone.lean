-- Prove2me | Theorems.Thm_BayesRouting_VOI_relative_value_sign_and_monotone
-- name    : BayesRouting.VOI.relative_value_sign_and_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T15:11:46.22993+00:00
-- url     : https://prove2.me/theorems/834270c7-7baf-42be-9fc2-f7894a8bbfe6
-- title:
--   Theorem 3 — sign of the relative value of information in the three regimes, and its monotonicity along $z^{ij}$
-- statement:
--   Let $\Gamma$ be a Bayesian routing game and $i\ne j$ two populations. Call a size vector $\lambda$ **admissible** if $\lambda^k\ge0$, $\sum_k\lambda^k=1$, $\lambda^i>0$ and $\lambda^j>0$. Let $\underline\lambda^i,\overline\lambda^i$ be the thresholds (23), and $V^{ij*}(\lambda)=C^{j*}(\lambda)-C^{i*}(\lambda)$ the relative value of information, evaluated at any BWE of $\Gamma(\lambda)$.
--
--   1. For every admissible $\lambda$ and every BWE of $\Gamma(\lambda)$:
--   $$V^{ij*}(\lambda)>0 \text{ if } \lambda^i<\underline\lambda^i,\qquad V^{ij*}(\lambda)=0 \text{ if } \underline\lambda^i\le\lambda^i\le\overline\lambda^i,\qquad V^{ij*}(\lambda)<0 \text{ if } \lambda^i>\overline\lambda^i .$$
--   2. $V^{ij*}$ is nonincreasing in the direction $z^{ij}$: if $\lambda$ and $\lambda+\varepsilon z^{ij}$ ($\varepsilon>0$) are admissible, then for every BWE $q$ of $\Gamma(\lambda)$ and every BWE $q'$ of $\Gamma(\lambda+\varepsilon z^{ij})$,
--   $$V^{ij*}(\lambda+\varepsilon z^{ij})\ \text{at } q'\ \le\ V^{ij*}(\lambda)\ \text{at } q .$$
--
--   So the population whose TIS has fewer subscribers relative to the thresholds (the minor population) enjoys lower equilibrium cost, both populations face the same cost in the middle regime, and the advantage of population $i$ shrinks as population $i$ grows at the expense of population $j$.
--
--   **Formalization Note** A BWE exists for every admissible $\lambda$ (item `bwe_exists`), so the quantification over BWE is not vacuous; by Theorem 1 the value of $V^{ij*}$ does not depend on which BWE is used. The model assumes every type profile has positive probability (added to the paper's assumptions).
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, p. 158, Theorem 3

import Mathlib
import Definitions.Def_BayesRouting_VOI_Game
import Definitions.Def_BayesRouting_VOI_Potential
import Definitions.Def_BayesRouting_VOI_Flows
import Definitions.Def_BayesRouting_VOI_Pairwise

namespace BayesRouting.VOI

/-- **Theorem 3** (Wu, Amin, Ozdaglar, Oper. Res. 69(1) 2021, p. 158). For two distinct populations
`i, j` and admissible size vectors (in the simplex, `λ^i > 0`, `λ^j > 0`), the relative value of
information `V^{ij*}(λ) = C^{j*}(λ) - C^{i*}(λ)`, evaluated at any BWE of `Γ(λ)`, is positive in
regime `Λ^{ij}_1` (`λ^i < λ̲^i`), zero in regime `Λ^{ij}_2` (`λ̲^i ≤ λ^i ≤ λ̄^i`) and negative in regime
`Λ^{ij}_3` (`λ̄^i < λ^i`). Furthermore, `V^{ij*}` is nonincreasing in the direction `z^{ij}`: for
`ε > 0` with `λ + ε z^{ij}` admissible, any BWE `q` of `Γ(λ)` and any BWE `q'` of
`Γ(λ + ε z^{ij})`, `V^{ij*}` at `q'` is at most `V^{ij*}` at `q`. -/
theorem relative_value_sign_and_monotone {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) (i j : I) (hij : i ≠ j) :
    (∀ lam ∈ stdSimplex ℝ I, 0 < lam i → 0 < lam j →
      ∀ q : (k : I) → T k → R → ℝ, IsBWE G lam q →
        (lam i < lowThr G lam i j → 0 < relValue G q i j) ∧
        (lowThr G lam i j ≤ lam i → lam i ≤ highThr G lam i j → relValue G q i j = 0) ∧
        (highThr G lam i j < lam i → relValue G q i j < 0)) ∧
    (∀ lam ∈ stdSimplex ℝ I, 0 < lam i → 0 < lam j →
      ∀ ε : ℝ, 0 < ε → 0 < (lam + ε • dir i j) j →
        ∀ q q' : (k : I) → T k → R → ℝ, IsBWE G lam q → IsBWE G (lam + ε • dir i j) q' →
          relValue G q' i j ≤ relValue G q i j) := by sorry

end BayesRouting.VOI
