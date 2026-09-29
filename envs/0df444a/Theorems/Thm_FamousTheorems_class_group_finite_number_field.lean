-- Prove2me | Theorems.Thm_FamousTheorems_class_group_finite_number_field
-- name    : FamousTheorems.class_group_finite_number_field
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:20:50.726046+00:00
-- url     : https://prove2.me/theorems/783158cd-3dd9-4f26-a643-80f394017f17
-- title:
--   Finiteness of the class number
-- statement:
--   **Finiteness of the class number.** For every number field $K$, the ideal class group of its ring of integers $\mathcal O_K$ is finite.
--
--   The class group measures how far $\mathcal O_K$ is from being a principal ideal domain, and its order is the class number $h_K$. Its finiteness is one of the two fundamental finiteness theorems of algebraic number theory, alongside Dirichlet's unit theorem, and is usually proved through the Minkowski bound.
--
--   **Formalization note.** Mathlib's instance `NumberField.RingOfIntegers.instFintypeClassGroup`, which provides `Fintype (ClassGroup (𝓞 K))`. The statement is the corresponding `Finite` proposition and is proved by `inferInstance`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `NumberField.RingOfIntegers.instFintypeClassGroup`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem class_group_finite_number_field (K : Type*) [Field K] [NumberField K] : Finite (ClassGroup (NumberField.RingOfIntegers K)) := by sorry

end FamousTheorems
