-- Prove2me | Theorems.Thm_ConstrNestedLogit_Space_ratio_inequality
-- name    : ConstrNestedLogit.Space.ratio_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:52.706985+00:00
-- url     : https://prove2.me/theorems/766ad551-1f33-4070-bdec-f1b5053c57f9
-- title:
--   Ratio inequality for full and fractional products
-- statement:
--   Suppose an optimal LP solution $x$ of (10) has exactly one fractional product $j_g$, and write $S^g=\{j:x_j=1\}$. Its full products have utility-to-space ratios at least that of $j_g$, hence
--
--   $$\sum_{j\in S^g}v_{ij}(r_{ij}-u)\ge\frac{v_{ij_g}(r_{ij_g}-u)}{w_{ij_g}}\sum_{j\in S^g}w_{ij}.$$
--
--   This comparison supports the refined space approximation when individual products are small relative to capacity.
--
--   **Formalization Note** Positive space weights make the displayed quotient meaningful.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 21, §5.2 displayed ratio inequality

import Mathlib
import Definitions.Def_ConstrNestedLogit_Space_Model

namespace ConstrNestedLogit.Space

/-- Full products have utility-to-space ratios at least that of the fractional product. -/
theorem ratio_inequality {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ k, 0 < I.v i k)
    (hw : ∀ k, 0 < w i k) (hwc : ∀ k, w i k ≤ c i)
    (u : ℝ) (hu : 0 ≤ u) (x : Fin n → ℝ)
    (hx : spaceLPOptimal I w c i u x) (j : Fin n)
    (hj : oneFractional x j) :
    utilityRatio I w i u j * (∑ k ∈ rounded x, w i k) ≤
      assortmentUtility I i u (rounded x) := by sorry

end ConstrNestedLogit.Space
