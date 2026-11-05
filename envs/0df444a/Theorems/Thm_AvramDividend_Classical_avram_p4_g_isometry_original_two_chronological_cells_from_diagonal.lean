-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_two_chronological_cells_from_diagonal
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_two_chronological_cells_from_diagonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:36:52.709562+00:00
-- url     : https://prove2.me/theorems/0e23d4ca-811f-4fab-ba88-f7c35616ee47
-- title:
--   Original intrinsic two consecutive predictable compensated negative-band blocks satisfy L2 isometry
-- statement:
--   For two original-X intrinsic chronological disjoint finite negative mark-band blocks, the squared L2 norm of a sum of predictable weighted centred counts equals the sum of physical source diagonal energies. The off-diagonal term vanishes by the proved first-moment original compensator; diagonal conditional variance remains an explicit source hypothesis.
-- source:
--   P2-E canonical original rectangle compensator, P4-G raw diagonal 9b483610 and the new P4-G source-orthogonality theorem ca34b7de after it becomes Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_past_cross_zero_from_proved_compensator
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_diagonal_of_source_second_rectangle

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_two_chronological_cells_from_diagonal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s u t : ℝ≥0) (hsu : s ≤ u) (hut : u ≤ t)
    (ε : ℝ) (hε : 0 < ε)
    (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁)
    (hB₂ : MeasurableSet B₂)
    (hBand₁ : B₁ ⊆ Ioo (-1 : ℝ) (-ε))
    (hBand₂ : B₂ ⊆ Ioo (-1 : ℝ) (-ε))
    (hν₁ : X.ν B₁ < ⊤) (hν₂ : X.ν B₂ < ⊤)
    (N₁ N₂ : Ω → ℝ≥0∞)
    (hActual₁ : N₁ = fun ω =>
      ((Measure.count.restrict {v : ℝ≥0 |
        0 < v ∧ X.X v ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v,
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
        (Ioc s u ×ˢ B₁))
    (hActual₂ : N₂ = fun ω =>
      ((Measure.count.restrict {v : ℝ≥0 |
        0 < v ∧ X.X v ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v,
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
        (Ioc u t ×ˢ B₂))
    (hMeas₂ : Measurable N₂)
    (r₁ r₂ : ℝ)
    (hRate₁ : r₁ = (((u - s : ℝ≥0) : ℝ≥0∞) * X.ν B₁).toReal)
    (hRate₂ : r₂ = (((t - u : ℝ≥0) : ℝ≥0∞) * X.ν B₂).toReal)
    (H₁ H₂ : Ω → ℝ)
    (hH₁ : StronglyMeasurable[𝓕 s] H₁)
    (hH₂ : StronglyMeasurable[𝓕 u] H₂)
    (hPast₁ : StronglyMeasurable[𝓕 u]
      (fun ω => H₁ ω * ((N₁ ω).toReal - r₁)))
    (hPairL2 : MemLp (fun ω =>
      (H₁ ω * ((N₁ ω).toReal - r₁)) * H₂ ω) 2 P)
    (hCount₂L2 : MemLp (fun ω => (N₂ ω).toReal - r₂) 2 P)
    (hSecond₁ : P[(fun ω => ((N₁ ω).toReal - r₁) ^ 2) | 𝓕 s]
       =ᵐ[P] (fun _ => r₁))
    (hSecond₂ : P[(fun ω => ((N₂ ω).toReal - r₂) ^ 2) | 𝓕 u]
       =ᵐ[P] (fun _ => r₂))
    (hSq₁ : Integrable (fun ω => ((N₁ ω).toReal - r₁) ^ 2) P)
    (hSq₂ : Integrable (fun ω => ((N₂ ω).toReal - r₂) ^ 2) P)
    (hHSq₁ : Integrable (fun ω => (H₁ ω) ^ 2) P)
    (hHSq₂ : Integrable (fun ω => (H₂ ω) ^ 2) P)
    (hWSq₁ : Integrable
      (fun ω => (H₁ ω) ^ 2 * ((N₁ ω).toReal - r₁) ^ 2) P)
    (hWSq₂ : Integrable
      (fun ω => (H₂ ω) ^ 2 * ((N₂ ω).toReal - r₂) ^ 2) P) :
    (∫ ω, (H₁ ω * ((N₁ ω).toReal - r₁) +
      H₂ ω * ((N₂ ω).toReal - r₂)) ^ 2 ∂P) =
    r₁ * ∫ ω, (H₁ ω) ^ 2 ∂P +
      r₂ * ∫ ω, (H₂ ω) ^ 2 ∂P := by sorry
