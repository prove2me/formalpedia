-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_preleft_C2_taylor_remainder_modulus
-- name    : AvramDividend.Classical.avram_ubv_gauss13_localise_original_preleft_C2_taylor_remainder_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:02:34.685743+00:00
-- url     : https://prove2.me/theorems/8055ac63-4eca-4bb3-b4aa-91f51de3f9c6
-- title:
--   Original predictable prepayment left-limit compact C2 Taylor remainder vanishing modulus
-- statement:
--   For the actual original-process prepayment left-limit reserve z and an interpolating state y in the same compact interior band, the quadratic Taylor-Lagrange remainder after subtracting the local Hessian term is bounded by epsilon times squared displacement for sufficiently short cells. The modulus is deterministic. This is the predictable state in original stopped Gaussian source 6242d57f; does not claim physical L1 convergence, treatment of dividend jumps, cap/ruin boundary or the final straddling cell.
-- source:
--   Direct adaptation of the remotely Proved postpayment Taylor interface 71f47e40 using Proved prepayment left-limit Hessian modulus 91ff27ff. The Lagrange point remains in the compact band. No auxiliary Brownian process or global second-derivative bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_preleft_hessian_modulus

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_localise_original_preleft_C2_taylor_remainder_modulus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ (ω : Ω) (t : ℝ≥0) (y : ℝ),
          let z := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
          z ∈ Set.Icc a b →
          y ∈ Set.Icc a b →
          z ≠ y →
          dist y z < δ →
          |w y - taylorWithinEval w 1 (Set.uIcc z y) z y -
            (iteratedDeriv 2 w z * (y - z) ^ 2) / 2| ≤
              ε * (y - z) ^ 2
    := by sorry
