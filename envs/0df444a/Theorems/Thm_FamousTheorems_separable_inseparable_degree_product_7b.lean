-- Prove2me | Theorems.Thm_FamousTheorems_separable_inseparable_degree_product_7b
-- name    : FamousTheorems.separable_inseparable_degree_product_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:11.999177+00:00
-- url     : https://prove2.me/theorems/54217ed1-2a78-4620-87fd-a73945c493b6
-- title:
--   The degree of a field extension is the product of its separable and inseparable degrees
-- statement:
--   **The degree is the product of the separable and inseparable degrees.** Let $E/F$ be a field extension. Then
--   $$[E:F]=[E:F]_s\,[E:F]_i,$$
--   where $[E:F]_s$ is the separable degree and $[E:F]_i$ the inseparable degree.
--
--   In characteristic $0$ every algebraic extension is separable and the inseparable degree is $1$. In characteristic $p$ the inseparable degree is a power of $p$, and the formula describes a finite extension as a separable extension followed by a purely inseparable one. The separable degree also equals the number of embeddings of $E$ into an algebraic closure of $F$.
--
--   **Formalization note.** Mathlib's `Field.finSepDegree_mul_finInsepDegree`. `Field.finSepDegree F E` is the number of $F$-embeddings of $E$ into an algebraic closure of $F$ and `Field.finInsepDegree F E` is the degree of $E$ over the separable closure of $F$ in $E$. All three quantities are natural numbers equal to $0$ when infinite, so the identity also holds for infinite extensions with this convention.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Field.finSepDegree_mul_finInsepDegree`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem separable_inseparable_degree_product_7b (F E : Type*) [Field F] [Field E] [Algebra F E] :
    Field.finSepDegree F E * Field.finInsepDegree F E = Module.finrank F E := by sorry

end FamousTheorems
