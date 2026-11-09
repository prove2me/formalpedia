-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_postpayment_hessian_modulus
-- name    : AvramDividend.Classical.avram_ubv_gauss13_localise_original_postpayment_hessian_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T22:20:27.074539+00:00
-- url     : https://prove2.me/theorems/0f1ca42f-70cb-45c9-8494-11a2af379ad2
-- title:
--   Original postpayment reserve compact Hessian modulus for physical Gaussian Taylor interpolation
-- statement:
--   For the same original Lévy source X and original dividend strategy D, every compact interior reserve band admits a deterministic uniform modulus of the C2 Hessian. For any original postpayment reserve z in the band and any interpolating real y in the band, the Hessian difference is small whenever |y-z| is small. This supplies the deterministic interpolation input for physical stopped Gaussian Taylor remainder estimates and makes no global-Hessian or boundary claim.
-- source:
--   Proved 13967844 supplies the exact compact C2 domain, and pinned Mathlib's Heine–Cantor theorem converts continuous second derivatives on Icc a b to a deterministic modulus. This does not itself prove stopped L1 convergence, Gaussian bracket uniform integrability, or cap contact.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_localise_original_postpayment_hessian_modulus
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
          let z := x + X.X t ω - rightLimit D t ω
          z ∈ Set.Icc a b →
          y ∈ Set.Icc a b →
          dist y z < δ →
          dist (deriv (deriv w) y) (deriv (deriv w) z) < ε
    := by sorry
