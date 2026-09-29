-- Prove2me | Theorems.Thm_FamousTheorems_number_field_product_formula
-- name    : FamousTheorems.number_field_product_formula
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:20:09.062109+00:00
-- url     : https://prove2.me/theorems/4abf041f-ae94-41a1-9ba2-71d4b38127e5
-- title:
--   The product formula for number fields
-- statement:
--   **The product formula for number fields.** Let $K$ be a number field and $x\in K$ nonzero. Then
--   $$\prod_{w\ \text{infinite}} |x|_w^{\,m_w}\cdot\prod_{w\ \text{finite}} |x|_w = 1,$$
--   where the first product runs over the infinite places of $K$ (with multiplicity $m_w=1$ for real places and $m_w=2$ for complex places) and the second over the finite places, normalised so that $|x|_{\mathfrak p}=N(\mathfrak p)^{-v_{\mathfrak p}(x)}$. Only finitely many factors differ from $1$.
--
--   This is the number-field analogue of the fact that a rational function has as many zeros as poles. It is the basis of height theory in Diophantine geometry and is one of the axioms of global fields.
--
--   **Formalization note.** Mathlib's `NumberField.prod_abs_eq_one`. The infinite product is a `Finset` product over `NumberField.InfinitePlace K` with exponent `w.mult`, and the finite product is a `finprod` over `NumberField.FinitePlace K`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `NumberField.prod_abs_eq_one`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem number_field_product_formula {K : Type*} [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
    (∏ w : NumberField.InfinitePlace K, w x ^ w.mult) * ∏ᶠ w : NumberField.FinitePlace K, w x = 1 := by sorry

end FamousTheorems
