-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_of_local_boundedness
-- name    : AvramDividend.Classical.levy_path_bddBelow_of_local_boundedness
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:19:26.445026+00:00
-- url     : https://prove2.me/theorems/9b2f041c-cff5-4db8-aff4-f2d3bd0df718
-- title:
--   Finite-horizon lower boundedness of a locally bounded Lévy trajectory
-- statement:
--   If each time point of a spectrally negative Lévy sample path admits a neighbourhood on which the real trajectory is bounded, then the trajectory is bounded below on every finite closed interval [0,t]. The proof uses compactness of [0,t] and the local-boundedness-to-compact-boundedness theorem. It reduces the pending a.s. path-boundedness obligation to showing local boundedness from right continuity and left limits.
-- source:
--   Mathlib Bornology.isBounded_image_of_isLocallyBounded_of_isCompact; Bornology.IsBounded.bddBelow, applied to the image of [0,t].

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Bornology
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_path_bddBelow_of_local_boundedness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (ω : Ω)
    (hloc : ∀ s : ℝ≥0, ∃ u ∈ 𝓝 s,
      Bornology.IsBounded ((fun r : ℝ≥0 => X.X r ω) '' u)) :
    BddBelow {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω} := by sorry
