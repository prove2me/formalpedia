-- Prove2me | Theorems.Thm_ConstrNestedLogit_UpperBound_proposition_7
-- name    : ConstrNestedLogit.UpperBound.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:51.027229+00:00
-- url     : https://prove2.me/theorems/a2101762-0cd9-438a-a1ba-f15293326320
-- title:
--   Proposition 7 — under space constraints, the optimal value of LP (13) is at least Z*
-- statement:
--   Consider the nested logit model with nests $M$, products $N = \{1, \dots, n\}$ in each nest, no-purchase weight $v_0 > 0$, preference weights $v_{ij} > 0$, arbitrary revenues $r_{ij}$ and dissimilarity parameters $\gamma_i \in (0, 1]$. For an assortment $(S_1, \dots, S_m)$ with $V_i(S_i) = \sum_{j \in S_i} v_{ij}$ and $R_i(S_i) = \sum_{j\in S_i} v_{ij} r_{ij} / V_i(S_i)$ (with $R_i(\bar 0) = 0$), the expected revenue is
--
--   $$\Pi(S_1, \dots, S_m) = \frac{\sum_{i \in M} V_i(S_i)^{\gamma_i} R_i(S_i)}{v_0 + \sum_{i \in M} V_i(S_i)^{\gamma_i}}.$$
--
--   Under space constraints product $j$ of nest $i$ needs $w_{ij} > 0$ units of space, nest $i$ has capacity $c_i$ with $w_{ij} \le c_i$ (p. 8), the feasible assortments of nest $i$ are $\mathcal C_i = \{S_i : \sum_{j \in S_i} w_{ij} \le c_i\}$, and $Z^* = \Pi(S_1^*, \dots, S_m^*)$ is the optimal value of problem (1), $\max\{\Pi(S_1,\dots,S_m) : S_i \in \mathcal C_i\ \forall i\}$.
--
--   Let $\{X_i : i \in M\}$ be finite sets of vectors such that every vector of $X_i$ is feasible for the linear programming relaxation of the knapsack problem (10) of nest $i$, and for every $u \ge 0$ some vector of $X_i$ is optimal for that relaxation at $u$ (the paper's $\{x_i^g : g \in \mathcal G_i\}$). If $(\hat z, \hat y)$ is an optimal solution of the linear program (13) built on these sets, then
--
--   $$\hat z \;\ge\; Z^*.$$
--
--   The linear program (13) thus gives a computable upper bound on the optimal expected revenue, against which the expected revenue of any heuristic assortment can be compared instance by instance.
--
--   **Formalization Note** The family $X_i$ is any finite family with the two properties above, a generalization of the paper's interval solutions $x_i^g$ that uses exactly what the proof needs. $Z^*$ is the revenue of a hypothesised optimal assortment `Sstar` of problem (1). The positivity of $v_0$ and of the $v_{ij}$ is added; the within-nest no-purchase weights are $0$, as in the paper's model. The paper's standing assumption $w_{ij} \le c_i$ (p. 8) is kept and the positivity $w_{ij} > 0$ is added; the proof needs them to make the zero vector feasible for each relaxation.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 33, Online Supplement A, Proposition 7

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_Relaxation
import Definitions.Def_ConstrNestedLogit_UpperBound_Relaxation
import Definitions.Def_ConstrNestedLogit_UpperBound_LP13

open NestedLogitVariants.General

namespace ConstrNestedLogit.UpperBound

/-- Proposition 7 (Online Supplement A, p. 33): under space constraints, if the vectors `X i`
(the paper's `{x_i^g : g ∈ G_i}`) are feasible for the linear programming relaxation of the
knapsack problem (10) and include an optimal solution of that relaxation for every `u ≥ 0`, and
`(ẑ, ŷ)` is an optimal solution of the linear program (13), then `ẑ ≥ Z*`, where
`Z* = Π(S*_1, …, S*_m)` is the optimal expected revenue of problem (1). -/
theorem proposition_7 {ι : Type*} [Fintype ι] {n : ℕ} (I : Instance ι n)
    (hvnp : ∀ i, I.vnp i = 0) (hv0 : 0 < I.v0) (hv : ∀ i j, 0 < I.v i j)
    (hγ : ∀ i, 0 < I.γ i ∧ I.γ i ≤ 1)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (X : ι → Finset (Fin n → ℝ))
    (hw : ∀ i j, 0 < w i j) (hwc : ∀ i j, w i j ≤ c i)
    (hX : IsRelaxSolutionFamily I w c X)
    (Sstar : ι → Finset (Fin n)) (hfeas : ∀ i, SpaceFeasible w c i (Sstar i))
    (hopt : ∀ S : ι → Finset (Fin n), (∀ i, SpaceFeasible w c i (S i)) →
      revenue I S ≤ revenue I Sstar)
    (zhat : ℝ) (yhat : ι → ℝ) (hzy : LP13Optimal I X zhat yhat) :
    revenue I Sstar ≤ zhat := by sorry

end ConstrNestedLogit.UpperBound
