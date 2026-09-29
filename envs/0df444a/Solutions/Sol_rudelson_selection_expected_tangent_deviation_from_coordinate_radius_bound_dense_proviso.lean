-- Prove2me | solution 1 for rudelson_selection_expected_tangent_deviation_from_coordinate_radius_bound_dense_proviso
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-23T22:21:51.667753+00:00
-- url     : https://prove2.me/submissions/8ee98945-b805-476c-8c4b-6545b8f3e183

import Theorems.Thm_selfbounding_resolution_quadratic_linear_bound
import Theorems.Thm_rudelson_selection_tangent_deviation_selfbounding_recursion_dense
import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
open MatrixCompletion

theorem solution :
    ∃ Csel : ℝ, 0 < Csel ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (S : SVD M r) (R : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        0 ≤ R →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) * (r : ℝ) *
          Real.log (↑(max n₁ n₂)) →
        Real.sqrt
            (Real.log (↑(max n₁ n₂)) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) * R ≤ 1 →
        (∀ i : Fin n₁, ∀ j : Fin n₂,
          frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ≤ R) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Csel *
            Real.sqrt
              (Real.log (↑(max n₁ n₂)) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            R := by
  obtain ⟨Cd, hCd, hdesym⟩ :=
    rudelson_selection_tangent_deviation_selfbounding_recursion_dense
  refine ⟨4 * (Cd + Cd ^ 2), by positivity, ?_⟩
  intro β hβ n₁ n₂ r m M S R hn₁ hn₂ hr hm hR hdens hproviso hcoord
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  set s : ℝ := Real.sqrt (Real.log (↑(max n₁ n₂)) / p) with hs
  set EZ : ℝ :=
    bernoulliExpectation p
      (fun Omega => tangentSamplingDeviation Omega S p) with hEZ
  -- desymmetrization core
  have hcore := hdesym β hβ n₁ n₂ r m M S R hn₁ hn₂ hr hm hR hdens hcoord
  obtain ⟨hnn, hrec⟩ := hcore
  -- hrec : EZ ≤ Cd*(s*R) + Cd*(s*R)*√EZ
  -- A0 := s*R, with proviso A0 ≤ 1 and 0 ≤ A0.
  have hsnn : 0 ≤ s := Real.sqrt_nonneg _
  have hA0nn : 0 ≤ s * R := mul_nonneg hsnn hR
  -- algebra brick
  have halg := selfbounding_resolution_quadratic_linear_bound EZ Cd (s * R)
    hnn (le_of_lt hCd) hA0nn hproviso hrec
  -- halg : EZ ≤ 4*(Cd+Cd^2)*(s*R)
  -- conclusion: EZ ≤ (4*(Cd+Cd^2)) * s * R
  calc EZ ≤ 4 * (Cd + Cd ^ 2) * (s * R) := halg
    _ = 4 * (Cd + Cd ^ 2) * s * R := by ring
