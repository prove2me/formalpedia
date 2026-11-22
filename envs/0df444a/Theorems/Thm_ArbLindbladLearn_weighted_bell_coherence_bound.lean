-- Prove2me | Theorems.Thm_ArbLindbladLearn_weighted_bell_coherence_bound
-- name    : ArbLindbladLearn.weighted_bell_coherence_bound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T01:06:31.654744+00:00
-- url     : https://prove2.me/theorems/0e18aed6-cb99-4e77-ae2a-07a511699d7a
-- title:
--   Weighted Bell coherences are bounded by the two Bell populations
-- statement:
--   For any finite nonnegative mixture of positive semidefinite Choi-space matrices, the square of the weighted sum of absolute Bell coherences is bounded by the product of the two weighted Bell populations. The matrix and weight families can vary arbitrarily, including zero populations.
-- source:
--   Supporting Lemma 3.5 of Chen and Yu, Learning Arbitrary Lindbladians from Time Evolution, section 3, arXiv:2607.28610.

import Mathlib
import Definitions.Def_ArbLindbladLearn_bellVec
open LindbladTolerant.Testing
open scoped ComplexOrder Matrix
open Classical

namespace ArbLindbladLearn

open Classical in
theorem weighted_bell_coherence_bound {n : ℕ} {ι : Type} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (J : ι → Op (Qubits n × Qubits n))
    (hJ : ∀ i ∈ s, (J i).PosSemidef) (u v : Qubits n × Qubits n → ℂ) :
    (∑ i ∈ s, w i * ‖bellForm (J i) u v‖)^2 ≤
      (∑ i ∈ s, w i * (bellForm (J i) u u).re) * (∑ i ∈ s, w i * (bellForm (J i) v v).re) := by sorry

end ArbLindbladLearn
