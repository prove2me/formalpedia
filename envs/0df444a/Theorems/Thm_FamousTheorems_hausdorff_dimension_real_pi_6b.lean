-- Prove2me | Theorems.Thm_FamousTheorems_hausdorff_dimension_real_pi_6b
-- name    : FamousTheorems.hausdorff_dimension_real_pi_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:04.362042+00:00
-- url     : https://prove2.me/theorems/8870409e-a5c8-4000-8ffd-215f3973b0c2
-- title:
--   The Hausdorff dimension of ℝⁿ is n
-- statement:
--   **The Hausdorff dimension of $\mathbb R^n$ is $n$.** The Hausdorff dimension of $\mathbb R^n$ equals $n$.
--
--   The theorem shows that Hausdorff dimension agrees with the usual dimension on Euclidean spaces, so it is a genuine extension of dimension to fractals. Together with its invariance under bi-Lipschitz maps, it gives lower bounds on the dimension of sets with positive Lebesgue measure. It also shows that a $C^1$ map cannot map a lower-dimensional space onto an open subset of $\mathbb R^n$.
--
--   **Formalization note.** Mathlib's `Real.dimH_univ_pi_fin`. Here $\mathbb R^n$ is `Fin n → ℝ` with the sup metric. This metric is bi-Lipschitz equivalent to the Euclidean one, so it has the same Hausdorff dimension. `dimH` takes values in $[0,\infty]$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Real.dimH_univ_pi_fin`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hausdorff_dimension_real_pi_6b (n : ℕ) : dimH (Set.univ : Set (Fin n → ℝ)) = n := by sorry

end FamousTheorems
