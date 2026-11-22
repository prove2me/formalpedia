-- Prove2me | Theorems.Thm_BornVolume_measure_bornCell
-- name    : BornVolume.measure_bornCell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:56.318453+00:00
-- url     : https://prove2.me/theorems/22b283b0-3fb8-4049-8310-9b6032e16e7c
-- title:
--   Born Volume: measure born Cell
-- statement:
--   **The Born cells have the Born weights as measures.** For a unitarily invariant probability
--   measure `μ` and a unit vector `ψ`, `μ (bornCell ψ i) = ‖ψᵢ‖²` for every `i`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornFrequency.lean#L139-L149
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornFrequency.lean#L139-L149

module
public import Definitions.Def_BornVolumeLean_Volume_BornWeight
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_BornVolumeLean_Volume_BornFrequency
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Set Filter Matrix Matrix.UnitaryGroup Projectivization
open scoped ENNReal
open BornVolume
variable {M : ℕ}

theorem BornVolume.measure_bornCell (μ : Measure (CPN (M + 1))) [IsProbabilityMeasure μ]
    (hμ : ∀ U : Matrix.unitaryGroup (Fin (M + 1)) ℂ, Measure.map (fun p => U • p) μ = μ)
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ : ‖ψ‖ = 1) (i : Fin (M + 1)) :
    μ (bornCell ψ i) = ENNReal.ofReal (‖ψ i‖ ^ 2) := by sorry
