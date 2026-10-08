-- Prove2me | Theorems.Thm_ConstrNestedLogit_Space_equation_11
-- name    : ConstrNestedLogit.Space.equation_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:59.363583+00:00
-- url     : https://prove2.me/theorems/83dde935-955c-4220-abaa-51ca371d5d95
-- title:
--   Knapsack rounding inequality (11)
-- statement:
--   Let $x$ be an optimal solution of the LP relaxation of (10) at $u\ge0$, with at most one fractional product $j_g$. Let $S^g=\{j:x_j=1\}$. For every feasible integer assortment $T$,
--
--   $$\sum_{j\in T}v_{ij}(r_{ij}-u)\le 2\max\left\{\sum_{j\in S^g}v_{ij}(r_{ij}-u),\ v_{ij_g}(r_{ij_g}-u)\right\}.$$
--
--   If there is no fractional product, the second argument of the maximum is zero. Thus either a rounded LP assortment or a singleton attains a two-approximation.
--
--   **Formalization Note** An optional index records whether the fractional product exists.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 20, equation (11)

import Mathlib
import Definitions.Def_ConstrNestedLogit_Space_Model

namespace ConstrNestedLogit.Space

/-- Equation (11), with an optional fractional coordinate. -/
theorem equation_11 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ j, 0 < I.v i j)
    (hw : ∀ j, 0 < w i j) (hwc : ∀ j, w i j ≤ c i)
    (u : ℝ) (hu : 0 ≤ u) (x : Fin n → ℝ)
    (hx : spaceLPOptimal I w c i u x) (j : Option (Fin n))
    (hj : ∀ k, (0 < x k ∧ x k < 1) ↔ j = some k) :
    ∀ T : Finset (Fin n), spaceFeasible w c i T →
      assortmentUtility I i u T ≤
        2 * max (assortmentUtility I i u (rounded x))
          (match j with | none => 0 | some k => utility I i u k) := by sorry

end ConstrNestedLogit.Space
