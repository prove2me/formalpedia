-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_root_slack_contraction_parameter
-- name    : AvramDividend.Classical.bv_esscher_root_slack_contraction_parameter
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:15:33.685783+00:00
-- url     : https://prove2.me/theorems/25e4360b-d064-42ce-970a-212a8fa3e793
-- title:
--   Strict contraction majorant for the drift-normalised BV Esscher renewal kernel
-- statement:
--   Given standing BV assumptions and a positive Esscher root, select a strictly positive real contraction constant rho below one and strictly above the real integral mass of the discounted jump-magnitude strict upper-tail kernel divided by the positive BV drift. The choice rho=(1+m/drift)/2 works even before proving strictly positive jump intensity. This is the geometrical pointwise bound parameter of the root-connected scaled renewal series data 9be5ada9, without an unnecessary positive-mass premise.
-- source:
--   Canonical Proved bv_standing_drift_pos, bv_esscher_root_subcritical_kernel_mass, and bv_esscher_positive_tail_real_total_mass_of_root.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_real_total_mass_of_root
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_root_slack_contraction_parameter
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ((∫ t in Ioi (0 : ℝ),
        ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) ∂volume) / X.drift) < ρ := by sorry
