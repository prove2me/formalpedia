-- Prove2me | Theorems.Thm_ConstrNestedLogit_Scheme_exists_optimal17_one_fractional
-- name    : ConstrNestedLogit.Scheme.exists_optimal17_one_fractional
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:07.756051+00:00
-- url     : https://prove2.me/theorems/10a81d39-903e-4176-aaa4-3d405be5aa70
-- title:
--   Problem (17) has an optimal solution with at most one fractional component
-- statement:
--   Fix a nest $i$, a parameter $u\ge 0$ and a set of products $J\subseteq N$. If the linear program (17) — maximize $\sum_j v_{ij}(r_{ij}-u)x_{ij}$ over $x\in[0,1]^n$ with $\sum_j w_{ij}x_{ij}\le c_i$, $x_{ij}=1$ for $j\in J$, and $x_{ik}=0$ for every $k\notin J$ whose utility exceeds $\min_{j\in J}v_{ij}(r_{ij}-u)$ — has a feasible point, then it has an optimal solution $x^\ast$ with
--
--   $$
--   \#\{\,j\in N : 0<x^\ast_{ij}<1\,\}\le 1 .
--   $$
--
--   The paper obtains such a solution with the greedy procedure that fills the knapsack in decreasing order of utility-to-space ratio; it is what makes the rounded-down assortment lose at most one product's utility.
--
--   **Formalization Note** Products are `Fin n`. No sign or ordering is assumed on the data.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 39, Online Supplement C.1, paragraph after (17)

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Scheme_Model

namespace ConstrNestedLogit.Scheme

/-- Online Supplement C.1, p. 39: whenever problem (17) is feasible, it has an optimal solution
with at most one fractional decision variable. -/
theorem exists_optimal17_one_fractional {ι : Type*} {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n) (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι)
    (u : ℝ) (hu : 0 ≤ u) (J : Finset (Fin n))
    (hfeas : ∃ y, feasible17 I w c i u J y) :
    ∃ x, optimal17 I w c i u J x ∧ (fractional x).card ≤ 1 := by sorry

end ConstrNestedLogit.Scheme
