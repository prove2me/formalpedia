-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_root_esscher_denominator_identity_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_root_esscher_denominator_identity_no_standing_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T04:41:11.950632+00:00
-- url     : https://prove2.me/theorems/d6d0dfcf-b942-4941-924b-df587bfc8fad
-- title:
--   Root-based Esscher denominator identity without standing (public)
-- statement:
--   For a bounded-variation spectrally negative Levy process with a positive Laplace root phi and positive drift, a fixed Esscher kernel satisfying the tail Laplace identity yields the discounted denominator identity above the root, with no Standing assumption.
-- source:
--   Source-faithful no-standing joint of the D4 origin-positivity proof (parent fc6b315a): exact statement of the standing tower lemma bv_esscher_fixed_kernel_denominator_identity (3bda821b, ACCEPTED proof DEN-tower) minus the Standing hypothesis, with the given root phi/hroot already in context and drift positivity hδ as an explicit hypothesis (discharged at the D4 top level by Open D1 p2m81_bv_root_drift_pos_no_standing_public e7c8659d). The monolithic D4 replay was refused by code_budget (172 executable lines over cap 100) plus complexity; this split follows the standing tower joints exactly. Proof replays DEN with Standing-free lemmas only.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_root_esscher_denominator_identity_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (φ : ℝ) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) (hδ : 0 < X.drift) (κ : Measure ℝ) (hκsf : SFinite κ)
    (hκsupp : κ (Iio (0 : ℝ)) = 0)
    (hκmass : κ Set.univ < ENNReal.ofReal X.drift)
    (hκLap : ∀ s : ℝ, 0 < s →
      (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(s * z))) ∂κ) =
      (∫⁻ z : ℝ≥0, ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
        ENNReal.ofReal ((1 - Real.exp (-(s * (z : ℝ)))) / s)
        ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))))) :
    ∀ θ : ℝ, max 0 (1 - φ) < θ →
      q < X.ψ (θ + φ) ∧
      ENNReal.ofReal ((X.ψ (θ + φ) - q)⁻¹) =
        ENNReal.ofReal (1 / θ) *
          ((ENNReal.ofReal X.drift)⁻¹ *
            (1 - (ENNReal.ofReal X.drift)⁻¹ *
              (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-θ * z)) ∂κ))⁻¹) := by sorry
