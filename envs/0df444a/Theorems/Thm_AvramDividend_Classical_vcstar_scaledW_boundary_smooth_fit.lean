-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_scaledW_boundary_smooth_fit
-- name    : AvramDividend.Classical.vcstar_scaledW_boundary_smooth_fit
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T16:53:53.527073+00:00
-- url     : https://prove2.me/theorems/640d249d-4982-45bb-9846-eaf47f432333
-- title:
--   Smooth-fit and Gaussian-weighted second-order matching at a positive optimal barrier
-- statement:
--   Assume a finite strictly positive barrier and the precise smoothness alternatives of Avram Theorem 2. The dividend candidate has the same first derivative as the scaled q-scale-function branch at c*, and their second derivatives agree after multiplication by the Gaussian variance sigma squared. This is the remaining analytic boundary-jet obligation in vcstar_scaledW_matched_weighted_jet_at_cstar once the pointwise branch equality below c* is discharged by the definitions. It requires Gaussian C2 smooth fit or bounded-variation first-order smooth fit and is independent of stochastic verification bounds.
-- source:
--   Source-faithful decomposition of authoritative theorem AvramDividend.Classical.vcstar_scaledW_matched_weighted_jet_at_cstar, UUID 22df0d92-75b1-47d8-928b-f82b6557a58d. Avram–Palmowski–Pistorius 2007, (5.1), (5.2), and Lemma 4. The parent additionally requires a separate piecewise-definitional equality below the barrier.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem vcstar_scaledW_boundary_smooth_fit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    deriv (vcstar W) (cstar W).toReal =
      deriv (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal ∧
    X.σ ^ 2 * iteratedDeriv 2 (vcstar W) (cstar W).toReal =
      X.σ ^ 2 * iteratedDeriv 2 (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal := by
  sorry

end AvramDividend.Classical
