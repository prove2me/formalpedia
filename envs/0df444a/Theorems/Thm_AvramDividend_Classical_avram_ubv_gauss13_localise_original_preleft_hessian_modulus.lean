-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_preleft_hessian_modulus
-- name    : AvramDividend.Classical.avram_ubv_gauss13_localise_original_preleft_hessian_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T23:24:30.463677+00:00
-- url     : https://prove2.me/theorems/91ff27ff-6123-4223-8bb4-5c753727498c
-- title:
--   Original predictable prepayment left-limit compact Hessian modulus for Gaussian stopped Taylor cells
-- statement:
--   For the original controlled spectrally negative Levy process and its original dividend strategy, if the actual prepayment left-limit reserve and a nearby interpolation point lie in a compact interior band, then their second iterated derivatives are uniformly close. The modulus is deterministic. This is the predictable state used by the original stopped Gaussian conditional Taylor cell 6242d57f, and does not assert stopped integrability or physical quadratic-tail convergence.
-- source:
--   Direct original-process pre-left adaptation of the Proved compact Hessian modulus 0f1ca42f, using the same Heine-Cantor argument and the verified pinned iteratedDeriv_succ identities. It keeps the actual left-limit reserve expression required by 6242d57f; no auxiliary Brownian source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_localise_original_preleft_hessian_modulus
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
          dist y z < δ →
          dist (iteratedDeriv 2 w y) (iteratedDeriv 2 w z) < ε := by sorry
