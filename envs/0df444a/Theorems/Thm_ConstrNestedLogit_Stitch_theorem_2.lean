-- Prove2me | Theorems.Thm_ConstrNestedLogit_Stitch_theorem_2
-- name    : ConstrNestedLogit.Stitch.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:24.955141+00:00
-- url     : https://prove2.me/theorems/d3a62ddf-351b-4e85-8582-c1a6eb3d353d
-- title:
--   Theorem 2: the LP-stitched assortment is best among candidate combinations
-- statement:
--   For each nest $i$, let $A_i$ be a finite collection of candidate assortments. Suppose $(\widehat z,\widehat y)$ is an optimal solution of linear program (4), which minimizes $z$ subject to $v_0z\ge\sum_i y_i$ and $y_i\ge V_i(S_i)^{\gamma_i}(R_i(S_i)-z)$ for every $S_i\in A_i$. In each nest, choose a candidate $\widehat S_i$ that maximizes $V_i(S_i)^{\gamma_i}(R_i(S_i)-\widehat z)$. Then
--
--   $$
--   \Pi(S_1,\ldots,S_m)\le\Pi(\widehat S_1,\ldots,\widehat S_m)
--   \qquad\text{for every combination }S_i\in A_i.
--   $$
--
--   Thus one LP optimum and independent nestwise maximizations select a highest-revenue combination from the supplied candidate collections.
--
--   **Formalization Note** Optimality in (4) means feasibility and minimum $z$ over every feasible LP pair; feasibility alone does not suffice. The paper's candidates lie in $C_i$, but no property of those sets is used in this comparison. Products are zero-indexed, $v_{i0}=0$, $v_0>0$, all product weights are positive, and $\gamma_i\in(0,1]$. Revenues need not be ordered or nonnegative.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 12, Theorem 2, equations (3)–(4)

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model

namespace ConstrNestedLogit.Stitch

/-- Theorem 2, p. 12: the candidate combination selected at an optimum of (4)
maximizes expected revenue among all candidate combinations. -/
theorem theorem_2 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (A : ι → Finset (Finset (Fin n)))
    (z : ℝ) (y : ι → ℝ) (S_hat : ι → Finset (Fin n))
    (hvnp : ∀ i, I.vnp i = 0)
    (hv0 : 0 < I.v0)
    (hv : ∀ i j, 0 < I.v i j)
    (hγ : ∀ i, 0 < I.γ i ∧ I.γ i ≤ 1)
    (hlp : NestedLogitVariants.LP.LP4Optimal I (fun i => (A i : Set (Finset (Fin n)))) z y)
    (hmem : ∀ i, S_hat i ∈ A i)
    (hmax : ∀ i S, S ∈ A i →
      NestedLogitVariants.LP.nestWeight I i S * (NestedLogitVariants.LP.R I i S - z) ≤
      NestedLogitVariants.LP.nestWeight I i (S_hat i) *
        (NestedLogitVariants.LP.R I i (S_hat i) - z)) :
    ∀ S : ι → Finset (Fin n), (∀ i, S i ∈ A i) →
      NestedLogitVariants.LP.revenue I S ≤ NestedLogitVariants.LP.revenue I S_hat := by sorry

end ConstrNestedLogit.Stitch
