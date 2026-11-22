-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_root_esscher_pointwise_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_root_esscher_pointwise_no_standing_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T04:41:19.953598+00:00
-- url     : https://prove2.me/theorems/a6505f4d-3210-4b9d-beff-34fcef60ddbe
-- title:
--   Root-based Esscher pointwise identity without standing (public)
-- statement:
--   For a bounded-variation spectrally negative Levy process with a positive Laplace root phi and positive drift, the canonical Esscher geometric renewal measure represents the exponentially tilted scale function pointwise on the positive axis, with no Standing assumption.
-- source:
--   Source-faithful no-standing joint of the D4 origin-positivity proof (parent fc6b315a): exact statement of the standing tower lemma bv_esscher_canonical_geometric_scale_pointwise (bd5082fb, ACCEPTED proof 323b71cb) minus the Standing hypothesis, with the given root phi/hroot already in context and drift positivity hδ as an explicit hypothesis (discharged at the D4 top level by Open D1 p2m81_bv_root_drift_pos_no_standing_public e7c8659d). The monolithic D4 replay was refused by code_budget (172 executable lines over cap 100) plus complexity; this split follows the standing tower joints exactly. Proof replays bd over the renewal-package and bridge children.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_root_esscher_pointwise_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (φ : ℝ) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) (hδ : 0 < X.drift) :
    ∃ (κ : Measure ℝ) (m : ℕ → Measure ℝ) (β : Measure ℝ),
      κ = (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t : ℝ =>
        ((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) ∧
      κ ≪ volume ∧
      m 0 = Measure.dirac (0 : ℝ) ∧
      (∀ n : ℕ, m (n + 1) = κ.conv (m n)) ∧
      (∀ n : ℕ, SFinite (m n)) ∧
      β = Measure.sum (fun n : ℕ =>
        (ENNReal.ofReal X.drift)⁻¹ ^ (n + 1) • m n) ∧
      0 < β Set.univ ∧ β Set.univ ≠ ⊤ ∧
      β (Iio (0 : ℝ)) = 0 ∧
      β.restrict (Ioi (0 : ℝ)) ≪ (volume : Measure ℝ) ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x →
        Real.exp (-(φ * x)) * W x = (β (Iic x)).toReal) := by sorry
