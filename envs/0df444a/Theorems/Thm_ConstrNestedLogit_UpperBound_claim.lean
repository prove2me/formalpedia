-- Prove2me | Theorems.Thm_ConstrNestedLogit_UpperBound_claim
-- name    : ConstrNestedLogit.UpperBound.claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:31.377975+00:00
-- url     : https://prove2.me/theorems/dca04f0d-faf4-411f-aed9-634e3ce6e598
-- title:
--   Online Supplement A, pp. 33–34 — the claim ŷ_i ≥ V_i(S*_i)^γ_i (R_i(S*_i) − ẑ)
-- statement:
--   Consider the nested logit model with no-purchase weight $v_0 > 0$, preference weights $v_{ij} > 0$, arbitrary revenues $r_{ij}$, dissimilarity parameters $\gamma_i \in (0, 1]$ and no within-nest no-purchase weight. Let $w_{ij} > 0$ be space requirements and $c_i$ capacities with $w_{ij} \le c_i$ for every product (the paper's standing assumption, p. 8), and let $\{X_i : i \in M\}$ be finite sets of vectors such that every vector of $X_i$ is feasible for the linear programming relaxation of the knapsack problem (10) of nest $i$, and for every $u \ge 0$ some vector of $X_i$ is optimal for that relaxation at $u$. Let $(S_1, \dots, S_m)$ be an assortment with $S_i \in \mathcal C_i$ for every nest. If $(z, y)$ is a feasible solution of the linear program (13) built on the sets $X_i$, then
--
--   $$y_i \;\ge\; V_i(S_i)^{\gamma_i}\big(R_i(S_i) - z\big) \qquad \text{for all } i \in M.$$
--
--   This is the claim at the heart of the proof of Proposition 7; summing it over the nests and using the first constraint of (13) gives the upper bound.
--
--   **Formalization Note** The paper states the claim for an optimal solution $(\hat z, \hat y)$ of (13) and an optimal assortment $(S_1^*, \dots, S_m^*)$ of problem (1); the statement here is for every feasible $(z, y)$ and every feasible assortment, which is what the proof uses. Positivity of $v_0$, $v_{ij}$ and $w_{ij}$ is added; $w_{ij} \le c_i$ is the paper's standing assumption (p. 8); $v_{i0} = 0$ is the paper's model.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, pp. 33–34, Online Supplement A, proof of Proposition 7 (the claim)

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_Relaxation
import Definitions.Def_ConstrNestedLogit_UpperBound_Relaxation
import Definitions.Def_ConstrNestedLogit_UpperBound_LP13

open NestedLogitVariants.General

namespace ConstrNestedLogit.UpperBound

/-- Online Supplement A, the claim in the proof of Proposition 7 (pp. 33–34): if the vectors `X i`
are feasible for the linear programming relaxation of (10) and include an optimal solution of that
relaxation for every `u ≥ 0`, then every feasible solution `(z, y)` of the linear program (13)
satisfies `y_i ≥ V_i(S_i)^{γ_i} (R_i(S_i) − z)` for every nest `i` and every assortment
`(S_1, …, S_m)` that satisfies the space constraints. -/
theorem claim {ι : Type*} [Fintype ι] {n : ℕ} (I : Instance ι n)
    (hvnp : ∀ i, I.vnp i = 0) (hv0 : 0 < I.v0) (hv : ∀ i j, 0 < I.v i j)
    (hγ : ∀ i, 0 < I.γ i ∧ I.γ i ≤ 1)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (X : ι → Finset (Fin n → ℝ))
    (hw : ∀ i j, 0 < w i j) (hwc : ∀ i j, w i j ≤ c i)
    (hX : IsRelaxSolutionFamily I w c X)
    (S : ι → Finset (Fin n)) (hS : ∀ i, SpaceFeasible w c i (S i))
    (z : ℝ) (y : ι → ℝ) (hzy : LP13Feasible I X z y) :
    ∀ i, nestWeight I i (S i) * (R I i (S i) - z) ≤ y i := by sorry

end ConstrNestedLogit.UpperBound
