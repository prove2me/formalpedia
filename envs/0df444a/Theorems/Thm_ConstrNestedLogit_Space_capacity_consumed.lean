-- Prove2me | Theorems.Thm_ConstrNestedLogit_Space_capacity_consumed
-- name    : ConstrNestedLogit.Space.capacity_consumed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:37.200808+00:00
-- url     : https://prove2.me/theorems/3977ad77-c9eb-4fb2-b907-6cc41ceb87da
-- title:
--   Capacity consumed by a positive fractional product
-- statement:
--   Suppose an optimal LP solution $x$ of (10) has exactly one fractional product $j_g$ and this product has positive utility. The rounded assortment $S^g=\{j:x_j=1\}$ then satisfies
--
--   $$\sum_{j\in S^g}w_{ij}+w_{ij_g}\ge c_i.$$
--
--   This expresses the paper's capacity-consumption step without assuming it for a zero-utility fractional product, which an optimal but non-greedy LP solution may contain.
--
--   **Formalization Note** The positive-utility condition is explicit because it is needed for the stated capacity conclusion.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 21, §5.2 paragraph before the ratio inequality

import Mathlib
import Definitions.Def_ConstrNestedLogit_Space_Model

namespace ConstrNestedLogit.Space

/-- A positive-utility fractional product can occur only when the LP fills the capacity. -/
theorem capacity_consumed {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ k, 0 < I.v i k)
    (hw : ∀ k, 0 < w i k) (hwc : ∀ k, w i k ≤ c i)
    (u : ℝ) (hu : 0 ≤ u) (x : Fin n → ℝ)
    (hx : spaceLPOptimal I w c i u x) (j : Fin n)
    (hj : oneFractional x j) (hpositive : 0 < utility I i u j) :
    c i ≤ (∑ k ∈ rounded x, w i k) + w i j := by sorry

end ConstrNestedLogit.Space
