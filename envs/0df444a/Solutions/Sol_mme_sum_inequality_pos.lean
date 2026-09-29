-- Prove2me | solution 1 for mme_sum_inequality_pos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-30T19:10:35.231596+00:00
-- url     : https://prove2.me/submissions/97c00d13-109f-4338-b0a9-b9d65c722178

import Theorems.Thm_mme_bridge_asymptoticRank
import Theorems.Thm_mme_mm_spectral_sum_inequality
import Theorems.Thm_mme_bridge_omega

/-! # Sketch: the all-positive concrete sum inequality

Assembled from the abstract asymptotic-spectrum sum inequality, instantiated at
`mmTensorData K` (`mme_mm_spectral_sum_inequality`), and the two bridges:

* `mme_bridge_asymptoticRank` — translate the concrete asymptotic-rank hypothesis into the
  abstract one (`asymptoticRank (tensorPreorder K) (∑ MMq …)`);
* `mme_bridge_omega` — replace the abstract exponent `(mmTensorData K).omegaAbs` by the
  Strassen-form `matMulExp_strassen K` in the conclusion. -/

open MME BigOperators

universe u

theorem solution {K : Type u} [Field K] {k : ℕ} (n m p : Fin k → ℕ)
    (hn : ∀ i, 1 ≤ n i) (hm : ∀ i, 1 ≤ m i) (hp : ∀ i, 1 ≤ p i) (r : ℕ)
    (h : tensorAsymptoticRank (TensorObj.bigAdd (fun i => MMObj K (n i) (m i) (p i))) ≤ r) :
    ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ (matMulExp_strassen K / 3) ≤ r := by
  -- Translate the hypothesis to the abstract asymptotic rank via bridge A.
  have h' : StrassenPreorder.asymptoticRank (tensorPreorder K)
      (∑ i, MMq K (n i) (m i) (p i)) ≤ r := by
    rw [mme_bridge_asymptoticRank n m p]; exact h
  -- Run the abstract sum inequality (instantiated at `mmTensorData K`).
  have hsum := mme_mm_spectral_sum_inequality n m p hn hm hp r h'
  -- Replace `omegaAbs` by `matMulExp_strassen K`.
  rwa [mme_bridge_omega] at hsum
