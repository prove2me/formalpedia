-- Prove2me | solution 1 for quadratic_neumann_last_index_distinct_centered_decoupling_transfer_general_sample
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-01T09:47:39.450764+00:00
-- url     : https://prove2.me/submissions/f441ff37-c588-404e-bbed-8b7ae8e0038a

import Theorems.Thm_quadratic_neumann_last_index_distinct_centered_pair_decoupling_tail_bound
import Theorems.Thm_quadratic_neumann_last_index_distinct_centered_original_tail_from_diagonal_decoupled_tail
import Mathlib.Tactic

open MatrixCompletion

/-!
Source: Candès–Recht 2008, Section 6.3, PDF pp. 31--32, the standard
two-variable decoupling argument for the centered
`ω₁ = ω₂ ≠ ω₃` quadratic chaos.

General-sample (constant/`Φ`-scale) pair→single transfer: a two-copy decoupled
estimate at an arbitrary nonnegative `scale` implies the corresponding one-copy
estimate, after enlarging the universal constant.  This is the §6.3 summary-scale
analogue of the `lam`-form
`quadratic_neumann_last_index_distinct_centered_decoupling_transfer`, built from
the same two generic transfers:

* `quadratic_neumann_last_index_distinct_centered_pair_decoupling_tail_bound`
  (pair → diagonal coupling, generic threshold/failure scale), and
* `quadratic_neumann_last_index_distinct_centered_original_tail_from_diagonal_decoupled_tail`
  (diagonal coupling → original, generic bound).
-/
theorem solution :
    ∃ Cdecouple cdecouple : ℝ, 0 < Cdecouple ∧ 0 < cdecouple ∧
      ∀ {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
        (S : SVD M r) (p Cdec cdec β scale : ℝ),
        0 ≤ p → p ≤ 1 → 0 < Cdec → 0 < cdec → 0 ≤ scale →
        bernoulliPairEventProb p
            (fun Omega1 Omega3 =>
              spectralNorm
                (quadraticNeumannLastIndexDistinctCenteredDecoupledContribution
                  Omega1 Omega3 S p) ≤
                Cdec * scale) ≥
          1 - cdec * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm
                (quadraticNeumannLastIndexDistinctCenteredContribution Omega S p) ≤
                (Cdecouple * Cdec) * scale) ≥
          1 - (cdecouple * cdec) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases quadratic_neumann_last_index_distinct_centered_pair_decoupling_tail_bound with
    ⟨K, L, hK, hL, hPair⟩
  refine ⟨K, L, hK, hL, ?_⟩
  intro n₁ n₂ r M S p Cdec cdec β scale hp0 hp1 hCdec hcdec hscale hDecoupled
  -- pair → diagonal coupling, generic threshold = scale, failure = N^{-β}
  have hDiagonal :=
    hPair S p Cdec cdec
      (Real.rpow (↑(max n₁ n₂)) (-β)) scale
      hp0 hp1 hCdec hcdec hDecoupled
  -- diagonal coupling → original contribution, generic bound = (K*Cdec)*scale
  exact
    quadratic_neumann_last_index_distinct_centered_original_tail_from_diagonal_decoupled_tail
      S p ((K * Cdec) * scale)
      (1 - (L * cdec) * Real.rpow (↑(max n₁ n₂)) (-β))
      hp0 hp1 hDiagonal
