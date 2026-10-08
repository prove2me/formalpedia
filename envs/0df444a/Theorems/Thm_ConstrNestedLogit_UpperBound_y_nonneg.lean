-- Prove2me | Theorems.Thm_ConstrNestedLogit_UpperBound_y_nonneg
-- name    : ConstrNestedLogit.UpperBound.y_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:37.944494+00:00
-- url     : https://prove2.me/theorems/9a213fa6-004a-44da-bca5-ed6ad9eeaef4
-- title:
--   Online Supplement A, p. 33 — every feasible solution of (13) has ŷ_i ≥ 0
-- statement:
--   Consider the nested logit model with preference weights $v_{ij} > 0$, arbitrary revenues $r_{ij}$, dissimilarity parameters $\gamma_i > 0$ and no within-nest no-purchase weight. Let $w_{ij} > 0$ be space requirements and $c_i$ capacities with $w_{ij} \le c_i$ for every product (the paper's standing assumption, p. 8), and let $\{X_i : i \in M\}$ be finite sets of vectors such that every vector of $X_i$ is feasible for the linear programming relaxation of the knapsack problem (10) of nest $i$, and for every $u \ge 0$ some vector of $X_i$ is optimal for that relaxation at $u$. If $(z, y)$ is a feasible solution of the linear program (13) built on these sets, then
--
--   $$y_i \ge 0 \qquad \text{for all } i \in M.$$
--
--   This is the first step of the proof of Proposition 7: it settles the claim $y_i \ge V_i(S_i^*)^{\gamma_i}(R_i(S_i^*) - z)$ whenever the right side is nonpositive.
--
--   **Formalization Note** The fact that the zero vector belongs to $X_i$ is not assumed; it follows from the two properties of the family. The statement is for every feasible $(z, y)$; the paper applies it to an optimal one. The positivity $v_{ij} > 0$ is added (the paper's weights are exponentials of utilities, p. 10, but positivity is not restated), and so is $v_{i0} = 0$, which is the paper's model. The paper's assumption $w_{ij} \le c_i$ (p. 8) is kept, and $w_{ij} > 0$ is added; together they make the zero vector feasible for every relaxation (without them, e.g. $w_{ij} < 0$ and $c_i < 0$, the conclusion fails).
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 33, Online Supplement A, proof of Proposition 7

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_Relaxation
import Definitions.Def_ConstrNestedLogit_UpperBound_Relaxation
import Definitions.Def_ConstrNestedLogit_UpperBound_LP13

open NestedLogitVariants.General

namespace ConstrNestedLogit.UpperBound

/-- Online Supplement A, proof of Proposition 7 (p. 33): if the vectors `X i` are feasible for
the linear programming relaxation of the knapsack problem (10) and include an optimal solution of
that relaxation for every `u ≥ 0`, then every feasible solution `(z, y)` of the linear program
(13) has `y_i ≥ 0` for every nest `i`. -/
theorem y_nonneg {ι : Type*} [Fintype ι] {n : ℕ} (I : Instance ι n)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ i j, 0 < I.v i j) (hγ : ∀ i, 0 < I.γ i)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (X : ι → Finset (Fin n → ℝ))
    (hw : ∀ i j, 0 < w i j) (hwc : ∀ i j, w i j ≤ c i)
    (hX : IsRelaxSolutionFamily I w c X) (z : ℝ) (y : ι → ℝ) (hzy : LP13Feasible I X z y) :
    ∀ i, 0 ≤ y i := by sorry

end ConstrNestedLogit.UpperBound
