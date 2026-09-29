-- Prove2me | solution 1 for quadratic_neumann_correction_from_index_partition_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T00:43:20.39014+00:00
-- url     : https://prove2.me/submissions/0bf405df-9414-4b3c-b398-2c21c853b12f

import Theorems.Thm_quadratic_neumann_correction_bound_from_index_partition_bounds
import Theorems.Thm_bernoulli_five_event_intersection_probability_from_lower_bounds
import Theorems.Thm_bernoulli_event_probability_mono
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion


open MatrixCompletion

/-- Intersect the five good events in the index-partition expansion (6.20),
then map the intersection through the deterministic spectral-norm triangle
bound for the second Neumann correction. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p C0 C123 C132 C112 Call c0 c123 c132 c112 call β lam : ℝ) :
    0 ≤ p → p ≤ 1 →
    0 < c0 → 0 < c123 → 0 < c132 → 0 < c112 → 0 < call →
    bernoulliEventProb p
        (fun Omega => spectralNorm (quadraticNeumannAllEqualContribution Omega S p) ≤
          C0 * Real.rpow lam (-((3 : ℝ) / 2))) ≥
        1 - c0 * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => spectralNorm (quadraticNeumannFirstIndexDistinctContribution Omega S p) ≤
          C123 * Real.rpow lam (-((3 : ℝ) / 2))) ≥
        1 - c123 * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => spectralNorm (quadraticNeumannMiddleIndexDistinctContribution Omega S p) ≤
          C132 * Real.rpow lam (-((3 : ℝ) / 2))) ≥
        1 - c132 * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => spectralNorm (quadraticNeumannLastIndexDistinctContribution Omega S p) ≤
          C112 * Real.rpow lam (-((3 : ℝ) / 2))) ≥
        1 - c112 * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤
          Call * Real.rpow lam (-((3 : ℝ) / 2))) ≥
        1 - call * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega =>
          NeumannCertificateTermSpectralBound Omega S p 2
            (((((C0 + C123) + C132) + C112) + Call) *
              Real.rpow lam (-((3 : ℝ) / 2)))) ≥
        1 - (((((c0 + c123) + c132) + c112) + call) *
          Real.rpow (↑(max n₁ n₂)) (-β)) := by
  intro hpNonneg hpLeOne _hc0 _hc123 _hc132 _hc112 _hcall
    h0Prob h123Prob h132Prob h112Prob hallProb
  have hIntersectionProb :=
    bernoulli_five_event_intersection_probability_from_lower_bounds
      p c0 c123 c132 c112 call (Real.rpow (↑(max n₁ n₂)) (-β))
      (fun Omega =>
        spectralNorm (quadraticNeumannAllEqualContribution Omega S p) ≤
          C0 * Real.rpow lam (-((3 : ℝ) / 2)))
      (fun Omega =>
        spectralNorm (quadraticNeumannFirstIndexDistinctContribution Omega S p) ≤
          C123 * Real.rpow lam (-((3 : ℝ) / 2)))
      (fun Omega =>
        spectralNorm (quadraticNeumannMiddleIndexDistinctContribution Omega S p) ≤
          C132 * Real.rpow lam (-((3 : ℝ) / 2)))
      (fun Omega =>
        spectralNorm (quadraticNeumannLastIndexDistinctContribution Omega S p) ≤
          C112 * Real.rpow lam (-((3 : ℝ) / 2)))
      (fun Omega =>
        spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤
          Call * Real.rpow lam (-((3 : ℝ) / 2)))
      hpNonneg hpLeOne h0Prob h123Prob h132Prob h112Prob hallProb
  have hMono :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm (quadraticNeumannAllEqualContribution Omega S p) ≤
                C0 * Real.rpow lam (-((3 : ℝ) / 2)) ∧
              spectralNorm (quadraticNeumannFirstIndexDistinctContribution Omega S p) ≤
                C123 * Real.rpow lam (-((3 : ℝ) / 2)) ∧
                spectralNorm (quadraticNeumannMiddleIndexDistinctContribution Omega S p) ≤
                  C132 * Real.rpow lam (-((3 : ℝ) / 2)) ∧
                  spectralNorm (quadraticNeumannLastIndexDistinctContribution Omega S p) ≤
                    C112 * Real.rpow lam (-((3 : ℝ) / 2)) ∧
                    spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤
                      Call * Real.rpow lam (-((3 : ℝ) / 2))) ≤
        bernoulliEventProb p
          (fun Omega =>
            NeumannCertificateTermSpectralBound Omega S p 2
              (((((C0 + C123) + C132) + C112) + Call) *
                Real.rpow lam (-((3 : ℝ) / 2)))) :=
    bernoulli_event_probability_mono p
      (fun Omega =>
        spectralNorm (quadraticNeumannAllEqualContribution Omega S p) ≤
            C0 * Real.rpow lam (-((3 : ℝ) / 2)) ∧
          spectralNorm (quadraticNeumannFirstIndexDistinctContribution Omega S p) ≤
            C123 * Real.rpow lam (-((3 : ℝ) / 2)) ∧
            spectralNorm (quadraticNeumannMiddleIndexDistinctContribution Omega S p) ≤
              C132 * Real.rpow lam (-((3 : ℝ) / 2)) ∧
              spectralNorm (quadraticNeumannLastIndexDistinctContribution Omega S p) ≤
                C112 * Real.rpow lam (-((3 : ℝ) / 2)) ∧
                spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤
                  Call * Real.rpow lam (-((3 : ℝ) / 2)))
      (fun Omega =>
        NeumannCertificateTermSpectralBound Omega S p 2
          (((((C0 + C123) + C132) + C112) + Call) *
            Real.rpow lam (-((3 : ℝ) / 2))))
      hpNonneg hpLeOne
      (by
        intro Omega hGood
        exact quadratic_neumann_correction_bound_from_index_partition_bounds
          S Omega p C0 C123 C132 C112 Call lam
          hGood.1 hGood.2.1 hGood.2.2.1 hGood.2.2.2.1 hGood.2.2.2.2)
  exact le_trans hIntersectionProb hMono
