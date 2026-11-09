-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_postpayment_C2_taylor_remainder_modulus
-- name    : AvramDividend.Classical.avram_ubv_gauss13_localise_original_postpayment_C2_taylor_remainder_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T23:09:33.532818+00:00
-- url     : https://prove2.me/theorems/71f47e40-44e4-4f22-b3e8-354521b02e90
-- title:
--   Original controlled compact C2 Taylor-Lagrange quadratic remainder has deterministic vanishing modulus
-- statement:
--   For original Lévy source X and original dividend strategy D, every compact interior postpayment reserve band admits a uniform quadratic Taylor remainder modulus. At genuine original reserve z and any different interpolating y in the same band, the difference between w(y) minus the order-one TaylorWithin evaluation at z and the half-Hessian quadratic term is bounded by epsilon times squared displacement whenever the displacement is sufficiently small. The theorem provides deterministic local Taylor error control on the physical state space, with no global Hessian or surrogate Brownian assumption. Stopped L1 summability, cap contact and final straddling remain separate.
-- source:
--   Derived from public Proved compact Hessian uniform continuity 0f1ca42f and pinned Mathlib taylor_mean_remainder_lagrange_iteratedDeriv for n=1; the Lagrange interpolation point lies inside the compact interior band. Explicitly conditioned on both physical and interpolating state remaining inside the band.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_postpayment_hessian_modulus

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_localise_original_postpayment_C2_taylor_remainder_modulus
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
          z ≠ y →
          dist y z < δ →
          |w y - taylorWithinEval w 1 (Set.uIcc z y) z y -
            (iteratedDeriv 2 w z * (y - z) ^ 2) / 2| ≤
              ε * (y - z) ^ 2
    := by sorry
