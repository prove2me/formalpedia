-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_preleft_compact_gaussian_finite_mesh_remainder
-- name    : AvramDividend.Classical.avram_ubv_gauss13_localise_original_preleft_compact_gaussian_finite_mesh_remainder
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:36:11.299195+00:00
-- url     : https://prove2.me/theorems/0f624bb1-2897-4b74-9cda-b61441d90c9a
-- title:
--   Original prepayment compact Gaussian finite-mesh Taylor error controlled by source quadratic energy
-- statement:
--   For the actual original X.X centred increments and prepayment left-limit reserve, any finite family of physically selected cells whose two endpoint states remain in one compact interior band and whose increments are uniformly short has total absolute C2 Taylor-remainder error at most epsilon times the sum of those exact Gaussian increment squares. The cell endpoints may depend on the path, so the final clipped cell is included if its compact and short hypotheses are proved. This is the deterministic physical mesh interface, not an assertion of L1 convergence or a claim that the floor of a stopping clock is a stopping time.
-- source:
--   Finite-cell sum of public Proved 8055ac63-4eca-4bb3-b4aa-91f51de3f9c6, retaining original filtration, X and D.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_preleft_C2_taylor_remainder_modulus

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_localise_original_preleft_compact_gaussian_finite_mesh_remainder
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (ω : Ω) (S : Finset ℕ) (s t : ℕ → ℝ≥0),
        let z : ℕ → ℝ := fun i =>
          Function.leftLim
            (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i)
        let g : ℕ → ℝ := fun i =>
          X.X (t i) ω - X.X (s i) ω - ((t i - s i) : ℝ) * X.c
        (∀ i ∈ S, z i ∈ Set.Icc a b ∧
          z i + g i ∈ Set.Icc a b ∧
          z i ≠ z i + g i ∧
          dist (z i + g i) (z i) < δ) →
        |∑ i ∈ S,
          (w (z i + g i) -
            taylorWithinEval w 1 (Set.uIcc (z i) (z i + g i))
              (z i) (z i + g i) -
            (iteratedDeriv 2 w (z i) * (g i) ^ 2) / 2)| ≤
          ε * ∑ i ∈ S, (g i) ^ 2 := by sorry
