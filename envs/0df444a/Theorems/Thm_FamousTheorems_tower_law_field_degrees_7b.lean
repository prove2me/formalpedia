-- Prove2me | Theorems.Thm_FamousTheorems_tower_law_field_degrees_7b
-- name    : FamousTheorems.tower_law_field_degrees_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:32:43.938061+00:00
-- url     : https://prove2.me/theorems/46ddb75c-00cd-4ff3-9e82-90fd99460a19
-- title:
--   Tower law: degrees of field extensions multiply
-- statement:
--   **The tower law.** Let $F\subseteq K\subseteq A$ be a tower of field extensions. Then
--   $$[A:F]=[A:K]\,[K:F].$$
--
--   The tower law is one of the most used facts in field theory. It gives the impossibility of the classical ruler-and-compass constructions: doubling the cube and trisecting the angle would require an element of degree $3$ inside a tower of quadratic extensions, whose degree is a power of $2$. The proof multiplies a basis of $K$ over $F$ with a basis of $A$ over $K$.
--
--   **Formalization note.** Mathlib's `Module.finrank_mul_finrank`. `Module.finrank` is $0$ for infinite-dimensional extensions, and the identity also holds with this convention when some degree is infinite. The scalar tower condition says that the three algebra structures are compatible.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Module.finrank_mul_finrank`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem tower_law_field_degrees_7b (F K A : Type*) [Field F] [Field K] [Field A] [Algebra F K] [Algebra K A] [Algebra F A]
    [IsScalarTower F K A] : Module.finrank F K * Module.finrank K A = Module.finrank F A := by sorry

end FamousTheorems
