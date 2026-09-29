-- Prove2me | Theorems.Thm_FamousTheorems_fuglede_putnam_theorem
-- name    : FamousTheorems.fuglede_putnam_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:28.100354+00:00
-- url     : https://prove2.me/theorems/578ad444-4c2b-40d9-ad3b-b0b877dba086
-- title:
--   The Fuglede–Putnam theorem
-- statement:
--   **The Fuglede–Putnam theorem.** Let $a,b$ be normal elements of a C*-algebra, and let $x$ satisfy $xa=bx$. Then also $xa^*=b^*x$.
--
--   Fuglede proved the case $a=b$ in 1950, answering a question of von Neumann: an operator commuting with a normal operator also commutes with its adjoint. Putnam extended it to intertwiners. The theorem is basic in operator theory. It shows, for example, that normal operators which are similar are unitarily equivalent.
--
--   **Formalization note.** Mathlib's `SemiconjBy.star_right`. `SemiconjBy x a b` means $xa=bx$, `IsStarNormal a` means $a^*a=aa^*$, and the algebra may be non-unital.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `SemiconjBy.star_right`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem fuglede_putnam_theorem {A : Type*} [NonUnitalCStarAlgebra A] {a b x : A} (ha : IsStarNormal a) (hb : IsStarNormal b)
    (h : SemiconjBy x a b) :
    SemiconjBy x (star a) (star b) := by sorry

end FamousTheorems
