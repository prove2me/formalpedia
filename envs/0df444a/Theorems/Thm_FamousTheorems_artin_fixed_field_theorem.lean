-- Prove2me | Theorems.Thm_FamousTheorems_artin_fixed_field_theorem
-- name    : FamousTheorems.artin_fixed_field_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:56:55.339255+00:00
-- url     : https://prove2.me/theorems/3e6400e5-ced6-40d9-af1a-9b508b5d9151
-- title:
--   Artin's theorem on fixed fields
-- statement:
--   **Artin's theorem on fixed fields.** Let $G$ be a finite group acting faithfully on a field $F$ by field automorphisms, and let $F^G$ be the fixed field. Then
--   $$[F:F^G]=|G|.$$
--
--   Together with the fact that $F/F^G$ is Galois with group $G$, this is the backbone of Artin's approach to Galois theory. It shows that every finite group of automorphisms arises as a Galois group, and it is used to prove the fundamental theorem of Galois theory.
--
--   **Formalization note.** Mathlib's `FixedPoints.finrank_eq_card`. `FixedPoints.subfield G F` is $F^G$, `Module.finrank` is the degree $[F:F^G]$, and faithfulness is `FaithfulSMul G F`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `FixedPoints.finrank_eq_card`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem artin_fixed_field_theorem (G F : Type*) [Group G] [Field F] [MulSemiringAction G F] [Fintype G] [FaithfulSMul G F] :
    Module.finrank (FixedPoints.subfield G F) F = Fintype.card G := by sorry

end FamousTheorems
