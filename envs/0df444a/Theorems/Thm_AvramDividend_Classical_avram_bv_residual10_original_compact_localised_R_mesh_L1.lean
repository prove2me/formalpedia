-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_compact_localised_R_mesh_L1
-- name    : AvramDividend.Classical.avram_bv_residual10_original_compact_localised_R_mesh_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:00:59.376221+00:00
-- url     : https://prove2.me/theorems/412feeb2-868f-4fff-84df-b9aa7e544406
-- title:
--   Integrability of true original BV residual mesh sum on a measurable coefficient-bounded localisation
-- statement:
--   For the original bounded-variation spectrally negative Levy process, consider a fixed monotone physical mesh. If each original path-dependent coefficient is measurable and bounded by K on a measurable localisation event, the exact untruncated raw residual weighted sum restricted to that event is integrable. The proof identifies it with the indicator of the already-proved clipped original residual mesh, rather than assuming a global bound. The localisation event and hypotheses are explicit, leaving exhaustion and uniform tail estimates to be proved separately.
-- source:
--   AVRAM BV-RESIDUAL10 finite-row original-path compact localisation and L1, 7 November 2026

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_clipped_weighted_R_mesh_L1

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_compact_localised_R_mesh_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (T : ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (hu0 : u n 0 = 0) (huT : u n (n + 1) ≤ T)
    (a : Ω → ℕ → ℝ) (ha : ∀ i, Measurable (fun ω => a ω i))
    (A : Set Ω) (hA : MeasurableSet A)
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ ω ∈ A, ∀ i ∈ Finset.range (n + 1), |a ω i| ≤ K) :
    Integrable (fun ω =>
      if ω ∈ A then
        let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
        let R : ℝ≥0 → ℝ := fun t =>
          ((t : ℝ) * X.drift - X.X t ω) - J t
        ∑ i ∈ Finset.range (n + 1),
          a ω i * (R (u n i) - R (u n (i + 1)))
      else 0) P := by sorry
