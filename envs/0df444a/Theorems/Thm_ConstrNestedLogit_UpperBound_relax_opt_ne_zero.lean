-- Prove2me | Theorems.Thm_ConstrNestedLogit_UpperBound_relax_opt_ne_zero
-- name    : ConstrNestedLogit.UpperBound.relax_opt_ne_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:38.57883+00:00
-- url     : https://prove2.me/theorems/6e200e14-31e6-4336-9c1c-cf8607c9e57f
-- title:
--   Online Supplement A, p. 34 — at û the zero vector is not optimal for the relaxation of (10)
-- statement:
--   Consider the nested logit model with preference weights $v_{ij} > 0$, arbitrary revenues $r_{ij}$ and no within-nest no-purchase weight, and fix a nest $i$ with $\gamma_i > 0$. Let $S$ be a nonempty assortment satisfying the space constraint $\sum_{j \in S} w_{ij} \le c_i$ and let $z$ be a real number with $R_i(S) > z$. Then the zero vector is **not** an optimal solution of the linear programming relaxation of the knapsack problem (10) of nest $i$ at
--
--   $$u = \hat u = \gamma_i\, z + (1 - \gamma_i)\, R_i(S).$$
--
--   In the proof of Proposition 7 this rules out the case $x_i^g = \bar 0$, so the chain of inequalities for a nonzero relaxation optimum always applies.
--
--   **Formalization Note** The positivity $v_{ij} > 0$ is an added hypothesis. The paper's argument passes through "$r_{ij} \le \hat u$ for all $j$"; the statement records the conclusion of that argument, that $0$ is not optimal.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 34, Online Supplement A, proof of Proposition 7 (case x_i^g = 0̄)

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_Relaxation
import Definitions.Def_ConstrNestedLogit_UpperBound_Relaxation
import Definitions.Def_ConstrNestedLogit_UpperBound_LP13

open NestedLogitVariants.General

namespace ConstrNestedLogit.UpperBound

/-- Online Supplement A, proof of Proposition 7 (p. 34): let `S` be a nonempty assortment
satisfying the space constraint of nest `i` with `R_i(S) > z`, and put
`û = γ_i z + (1 − γ_i) R_i(S)` with `γ_i > 0`. Then the zero vector is not an optimal solution of
the linear programming relaxation of the knapsack problem (10) at `u = û`. -/
theorem relax_opt_ne_zero {ι : Type*} {n : ℕ} (I : Instance ι n)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ i j, 0 < I.v i j)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι) (hγ : 0 < I.γ i)
    (S : Finset (Fin n)) (hS : SpaceFeasible w c i S) (hSne : S.Nonempty)
    (z : ℝ) (hRz : z < R I i S) :
    ¬ RelaxOptimal I w c i (I.γ i * z + (1 - I.γ i) * R I i S) 0 := by sorry

end ConstrNestedLogit.UpperBound
