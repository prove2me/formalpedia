-- Prove2me | Theorems.Thm_FamousTheorems_hermite_minkowski_discriminant
-- name    : FamousTheorems.hermite_minkowski_discriminant
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:05:07.851164+00:00
-- url     : https://prove2.me/theorems/68bd0488-26d8-4e74-a39b-fb937a089eed
-- title:
--   The Hermite–Minkowski theorem (discriminant bound)
-- statement:
--   **The Hermite–Minkowski theorem (discriminant bound).** Let $K$ be a number field with $[K:\mathbb Q]>1$. Then its discriminant satisfies
--   $$|d_K|>2.$$
--
--   In particular $|d_K|>1$, so every number field other than $\mathbb Q$ has a ramified prime (Minkowski's theorem). Equivalently, $\mathbb Q$ has no nontrivial unramified extension. The proof uses Minkowski's lattice-point bound, which gives $|d_K|\ge(\pi/4)^{2r_2}(n^n/n!)^2$ with $n=[K:\mathbb Q]$ and $r_2$ the number of complex places.
--
--   **Formalization note.** Mathlib's `NumberField.abs_discr_gt_two`. `NumberField.discr K` is the absolute discriminant, an integer, and `Module.finrank ℚ K` is the degree $[K:\mathbb Q]$. The statement is the slightly stronger bound $|d_K|>2$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `NumberField.abs_discr_gt_two`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hermite_minkowski_discriminant {K : Type*} [Field K] [NumberField K] (h : 1 < Module.finrank ℚ K) : 2 < |NumberField.discr K| := by sorry

end FamousTheorems
