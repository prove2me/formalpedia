-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexSets_discrete_separation_submodular
-- name    : DiscreteConvex.MConvexSets.discrete_separation_submodular
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:18:46.055748+00:00
-- url     : https://prove2.me/theorems/7562e306-9469-4c09-b3ce-489782b71a1e
-- title:
--   Theorem 4.17 -- Frank's discrete separation theorem
-- statement:
--   **Theorem 4.17** (Frank, p.111). Let $\rho : 2^V \to \mathbb R \cup \{+\infty\}$ and $\mu : 2^V \to \mathbb R \cup \{-\infty\}$ be submodular and supermodular, respectively, with $\rho(X) \ge \mu(X)$ for all $X \subseteq V$. Then there is $x^* \in \mathbb R^V$ with $\rho(X) \ge x^*(X) \ge \mu(X)$ for all $X$; moreover, if $\rho$ and $\mu$ are integer valued, $x^*$ can be chosen integer valued. This is derived, in the book, as a corollary of Theorem 4.18 (Edmonds's intersection theorem) applied to $\rho_1 = \rho$, $\rho_2(X) = \mu(V) - \mu(V\setminus X)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.111, Theorem 4.17.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.111, Theorem 4.17

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSets_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSets_SupermodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSets_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexSets_IsIntegerValuedBot
import Definitions.Def_DiscreteConvex_MConvexSets_ToEReal
import Definitions.Def_DiscreteConvex_MConvexSets_ToERealOfBot

namespace DiscreteConvex.MConvexSets

/-- Theorem 4.17 (Frank's discrete separation theorem; Murota, *Discrete Convex Analysis*,
SIAM 2003, p.111). Let `ρ : 2ⱽ → R ∪ {+∞}` and `μ : 2ⱽ → R ∪ {-∞}` be submodular and
supermodular, respectively, with `ρ(X) ≥ μ(X)` for all `X ⊆ V`. Then there is `x* ∈ Rⱽ` with
`ρ(X) ≥ x*(X) ≥ μ(X)` for all `X`; moreover, if `ρ` and `μ` are integer valued, `x*` can be
chosen integer valued. -/
theorem discrete_separation_submodular {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (μ : Finset V → WithBot ℝ)
    (hρ : SubmodularSetFunction ρ) (hμ : SupermodularSetFunction μ)
    (hsep : ∀ X : Finset V, ToERealOfBot (μ X) ≤ ToEReal (ρ X)) :
    (∃ x : V → ℝ, ∀ X : Finset V,
        ToERealOfBot (μ X) ≤ ToEReal (((∑ v ∈ X, x v : ℝ) : WithTop ℝ)) ∧
        ToEReal (((∑ v ∈ X, x v : ℝ) : WithTop ℝ)) ≤ ToEReal (ρ X)) ∧
    (IsIntegerValued ρ → IsIntegerValuedBot μ →
      ∃ x : V → ℤ, ∀ X : Finset V,
        ToERealOfBot (μ X) ≤ ToEReal (((∑ v ∈ X, (x v : ℝ) : ℝ) : WithTop ℝ)) ∧
        ToEReal (((∑ v ∈ X, (x v : ℝ) : ℝ) : WithTop ℝ)) ≤ ToEReal (ρ X)) := by sorry

end DiscreteConvex.MConvexSets
