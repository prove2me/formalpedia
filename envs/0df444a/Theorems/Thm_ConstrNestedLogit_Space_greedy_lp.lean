-- Prove2me | Theorems.Thm_ConstrNestedLogit_Space_greedy_lp
-- name    : ConstrNestedLogit.Space.greedy_lp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:36.913904+00:00
-- url     : https://prove2.me/theorems/2dbfdae9-f404-49d2-a12d-436df861fdd6
-- title:
--   Greedy optimum of the continuous knapsack relaxation
-- statement:
--   For a nest with positive product preference and space weights, every product individually fitting the capacity, and every $u\ge0$, the LP relaxation of (10) has an optimal solution $x$ with at most one fractional coordinate. It can be chosen so that each selected product has strictly positive utility, and no unfilled product has a larger utility-to-space ratio than a selected product:
--
--   $$0<x_j,\ x_k<1\quad\Longrightarrow\quad f_{ik}(u)\le f_{ij}(u).$$
--
--   This is the greedy structure used to build a finite family of rounded LP assortments.
--
--   **Formalization Note** The product set is nonempty, $w_{ij}>0$, and $v_{ij}>0$; positivity of the weights makes the ratios defined.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 19, §5.1 paragraph after (10)

import Mathlib
import Definitions.Def_ConstrNestedLogit_Space_Model

namespace ConstrNestedLogit.Space

/-- The greedy LP relaxation of (10) can be chosen with at most one fractional coordinate. -/
theorem greedy_lp {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι)
    (hn : 0 < n)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ j, 0 < I.v i j)
    (hw : ∀ j, 0 < w i j) (hwc : ∀ j, w i j ≤ c i)
    (u : ℝ) (hu : 0 ≤ u) :
    ∃ x : Fin n → ℝ, spaceLPOptimal I w c i u x ∧ atMostOneFractional x ∧
      (∀ j, 0 < x j → 0 < utility I i u j) ∧
      (∀ j k, 0 < x j → x k < 1 →
        utilityRatio I w i u k ≤ utilityRatio I w i u j) := by sorry

end ConstrNestedLogit.Space
