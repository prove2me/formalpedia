-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_scaledW_matched_weighted_jet_at_cstar
-- name    : AvramDividend.Classical.vcstar_scaledW_matched_weighted_jet_at_cstar
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T23:28:52.244177+00:00
-- url     : https://prove2.me/theorems/22df0d92-75b1-47d8-928b-f82b6557a58d
-- title:
--   Optimal barrier candidate and scaled W agree below c-star with matching Gaussian-weighted boundary jet
-- statement:
--   The positive finite optimal barrier candidate v_{c*} coincides with its scaled scale-function branch u=W/W'(c*) for every reserve z≤c*, including negative reserves where W and v vanish. At c* the first derivatives agree by smooth fit. Since σ² multiplies the Gaussian term in the generator, only σ²-weighted second-derivative matching is needed: automatic for bounded variation (σ=0), and supplied by Gaussian C2 smooth-fit and derivative minimisation when σ>0. This isolates exactly the source-specific boundary jet analysis needed to invoke the source-neutral generator_eq_at_barrier_of_weighted_jet lemma.
-- source:
--   Avram, Palmowski and Pistorius (2007), (5.1)-(5.2), Lemma 3, Lemma 4 and Theorem 2: matching scale and affine branches at the optimising barrier.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem vcstar_scaledW_matched_weighted_jet_at_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    (∀ z : ℝ, z ≤ (cstar W).toReal →
      vcstar W z = (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal)) z) ∧
    deriv (vcstar W) (cstar W).toReal =
      deriv (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal ∧
    X.σ ^ 2 * iteratedDeriv 2 (vcstar W) (cstar W).toReal =
      X.σ ^ 2 * iteratedDeriv 2 (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal := by
  sorry
end AvramDividend.Classical
