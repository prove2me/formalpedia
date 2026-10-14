-- Prove2me | Theorems.Thm_DRUQChance_Markov_theorem_3_if
-- name    : DRUQChance.Markov.theorem_3_if
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T18:48:47.759969+00:00
-- url     : https://prove2.me/theorems/d99ca628-57a3-4593-96cf-51773d47f666
-- title:
--   Theorem 3 (case I = 1), sufficiency — every feasible point of (17) bounds the worst-case probability from below
-- statement:
--   Let $\mathcal P$ be a Markov ambiguity set: the set of probability distributions $\mathbb P$ of $(\tilde z,\tilde u) \in \mathbb R^P\times\mathbb R^Q$ with $\mathbb E_{\mathbb P}[A\tilde z + B\tilde u] = b$ and $\mathbb P[(\tilde z,\tilde u) \in \mathcal C_1] = 1$, where $\mathcal C_1 = \{(z,u) : C_1 z + D_1 u \preccurlyeq_{\mathcal K_1} d_1\}$ and $\mathcal K_1$ is a proper cone (closed, convex, pointed, with nonempty interior).
--   Let $S \in \mathbb R^{J\times P}$ have rows $s_j^\top$ and let $t \in \mathbb R^J$. If $(\gamma,\lambda,\kappa,\phi,\tau,\psi)$ is feasible in the conic program (17) with $I = 1$, then for every $\mathbb P \in \mathcal P$
--   $$b^\top\gamma + \underline p_1\lambda - \overline p_1\kappa \;\le\; \mathbb P[S\tilde z \le t].$$
--   Equivalently, the optimal value of (17) never exceeds the worst-case probability (1).
--
--   This is the weak-duality half of Theorem 3 of the paper in the case of a single confidence set: feasible points of (17) are certified lower bounds on the probability of safe operation. The paper states Theorem 3 for general nested ambiguity sets; only the case $I = 1$ is formalized here, because that is the only case in which the paper spells out the Slater condition (S).
--
--   The paper's hypotheses (B), (N) are automatic for $I = 1$ with $\underline p_1 = \overline p_1 = 1$. The statement does not assume (S) or essential strict feasibility of $\mathcal C_1$, which this direction does not need; this only strengthens it.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`; the paper's single confidence set ($I = 1$) is the index `0 : Fin 1` of `AmbData nP nQ nK 0` from the published module `DRConvexOpt.Reform.Setting`, whose field `c 0` is the paper's $d_1$ and whose `plo 0`, `phi 0` are $\underline p_1$, $\overline p_1$. $\mathbb P[\cdot]$ is `μ.real`. The local `paperAmbiguitySet` retains the reused data and confidence sets, but requires integrability only of $A\tilde z+B\tilde u$, exactly the moment in (4); when $K=0$, this condition is void as the paper states on p. 6.
-- source:
--   Hanasusanto, Roitch, Kuhn & Wiesemann, A distributionally robust perspective on uncertainty quantification and chance constrained programming, Math. Program. 151(1) (2015); authors' accepted manuscript, pp. 11–12, Theorem 3 (case I = 1, sufficiency direction) and (17)

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting
import Definitions.Def_DRUQChance_Markov_Basic

namespace DRUQChance.Markov

open MeasureTheory Matrix DRConvexOpt.Reform

/-- Theorem 3 at `I = 1`, sufficiency (pp. 11–12): for a Markov ambiguity set with proper cone
`K₁`, the objective value of every feasible point of (17) is at most `ℙ[S z̃ ≤ t]` for every
`ℙ` in the ambiguity set. -/
theorem theorem_3_if {nP nQ nK nJ : ℕ} (amb : AmbData nP nQ nK 0) (hM : IsMarkov amb)
    (hK : IsProperCone (amb.K 0)) (S : Matrix (Fin nJ) (Fin nP) ℝ) (t : Fin nJ → ℝ)
    (γ : Fin nK → ℝ) (lam kap : ℝ) (φ : Fin (amb.L 0) → ℝ) (τ : Fin nJ → ℝ)
    (ψ : Fin nJ → Fin (amb.L 0) → ℝ) (hfeas : UQFeasible amb S t γ lam kap φ τ ψ)
    (μ : Measure ((Fin nP → ℝ) × (Fin nQ → ℝ))) (hμ : μ ∈ paperAmbiguitySet amb) :
    uqObjective amb γ lam kap ≤ μ.real {ω | S *ᵥ ω.1 ≤ t} := by sorry

end DRUQChance.Markov
