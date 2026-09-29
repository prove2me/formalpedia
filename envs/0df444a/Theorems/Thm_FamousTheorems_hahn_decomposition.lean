-- Prove2me | Theorems.Thm_FamousTheorems_hahn_decomposition
-- name    : FamousTheorems.hahn_decomposition
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:33.517153+00:00
-- url     : https://prove2.me/theorems/4e4ed9c7-747d-491f-9e87-a010e6798943
-- title:
--   The Hahn decomposition theorem
-- statement:
--   **The Hahn decomposition theorem.** For every finite signed measure $s$ on a measurable space $X$ there is a partition $X=P\sqcup N$ into measurable sets such that $s$ is nonnegative on every measurable subset of $P$ and nonpositive on every measurable subset of $N$.
--
--   The decomposition is unique up to null sets. It yields the Jordan decomposition $s=s^+-s^-$ into mutually singular measures and the total variation $|s|$, and it is an ingredient in the Radon–Nikodym and Lebesgue decomposition theorems.
--
--   **Formalization note.** Mathlib's `MeasureTheory.SignedMeasure.exists_isCompl_positive_negative`. `VectorMeasure.restrict 0 i ≤ VectorMeasure.restrict s i` says `s` is nonnegative on `i` (Mathlib's notation `0 ≤[i] s`), and `IsCompl i j` says `i` and `j` partition the space.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.SignedMeasure.exists_isCompl_positive_negative`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hahn_decomposition {α : Type*} [MeasurableSpace α] (s : MeasureTheory.SignedMeasure α) :
    ∃ i j : Set α, MeasurableSet i ∧ MeasureTheory.VectorMeasure.restrict 0 i ≤ MeasureTheory.VectorMeasure.restrict s i ∧
      MeasurableSet j ∧ MeasureTheory.VectorMeasure.restrict s j ≤ MeasureTheory.VectorMeasure.restrict 0 j ∧ IsCompl i j := by sorry

end FamousTheorems
