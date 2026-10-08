-- Prove2me | Theorems.Thm_ConstrNestedLogit_UpperBound_key_inequality
-- name    : ConstrNestedLogit.UpperBound.key_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:17.204108+00:00
-- url     : https://prove2.me/theorems/eea3ff4f-64de-4422-b535-d7ce3aa0ae30
-- title:
--   Online Supplement A, pp. 33–34 — the chain of inequalities for a nonzero relaxation optimum
-- statement:
--   Consider the nested logit model with preference weights $v_{ij} > 0$, arbitrary revenues $r_{ij}$ and no within-nest no-purchase weight, and fix a nest $i$ with $\gamma_i \in (0, 1]$. Let $S$ be a nonempty assortment satisfying the space constraint $\sum_{j \in S} w_{ij} \le c_i$, let $z$ be a real number with $R_i(S) > z$, and set
--
--   $$\hat u = \gamma_i\, z + (1 - \gamma_i)\, R_i(S).$$
--
--   If $x \ne 0$ is an optimal solution of the linear programming relaxation of the knapsack problem (10) of nest $i$ at $u = \hat u$, then, writing $V_i(x) = \sum_j v_{ij} x_j$ and $R_i(x) = \sum_j v_{ij} r_{ij} x_j / V_i(x)$,
--
--   $$V_i(x)^{\gamma_i}\big(R_i(x) - z\big) \;\ge\; V_i(S)^{\gamma_i}\big(R_i(S) - z\big).$$
--
--   This is the first and last link of the chain of inequalities in the proof of Proposition 7; together with a constraint of the linear program (13), it gives the proof's claim in the case $x_i^g \ne \bar 0$.
--
--   **Formalization Note** The left side is the published `NestedLogitVariants.General.F I i x z`, which equals the displayed term because $v_{i0} = 0$. The positivity $v_{ij} > 0$ is an added hypothesis.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, pp. 33–34, Online Supplement A, proof of Proposition 7 (chain of inequalities)

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_Relaxation
import Definitions.Def_ConstrNestedLogit_UpperBound_Relaxation
import Definitions.Def_ConstrNestedLogit_UpperBound_LP13

open NestedLogitVariants.General

namespace ConstrNestedLogit.UpperBound

/-- Online Supplement A, proof of Proposition 7 (pp. 33–34), the chain of inequalities: let
`γ_i ∈ (0, 1]`, let `S` be a nonempty assortment satisfying the space constraint of nest `i` with
`R_i(S) > z`, put `û = γ_i z + (1 − γ_i) R_i(S)`, and let `x ≠ 0` be an optimal solution of the
linear programming relaxation of (10) at `û`. Then
`V_i(x)^{γ_i} (R_i(x) − z) ≥ V_i(S)^{γ_i} (R_i(S) − z)`, where the left side is `F I i x z`. -/
theorem key_inequality {ι : Type*} {n : ℕ} (I : Instance ι n)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ i j, 0 < I.v i j)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι) (hγ : 0 < I.γ i ∧ I.γ i ≤ 1)
    (S : Finset (Fin n)) (hS : SpaceFeasible w c i S) (hSne : S.Nonempty)
    (z : ℝ) (hRz : z < R I i S) (x : Fin n → ℝ)
    (hx : RelaxOptimal I w c i (I.γ i * z + (1 - I.γ i) * R I i S) x) (hx0 : x ≠ 0) :
    nestWeight I i S * (R I i S - z) ≤ F I i x z := by sorry

end ConstrNestedLogit.UpperBound
