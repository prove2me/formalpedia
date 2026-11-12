-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb59_finite_L2_MDS_zero_extension
-- name    : AvramDividend.Classical.avram_gb59_finite_L2_MDS_zero_extension
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:01:09.430799+00:00
-- url     : https://prove2.me/theorems/9c3a1a0a-f3c2-49b1-8ef3-e0b18eae2deb
-- title:
--   Zero extension preserves all square-integrable martingale difference conditions
-- statement:
--   A finite family of adapted square-integrable martingale differences for any fixed discrete filtration can be extended by zero to all natural indices while retaining square integrability, successor-time measurability, and conditional centring. This permits the original finite Gaussian grid to use standard all-time martingale difference orthogonality.

import Mathlib
open MeasureTheory

theorem AvramDividend.Classical.avram_gb59_finite_L2_MDS_zero_extension
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (𝓖 : Filtration ℕ mΩ)
    (m : ℕ) (U : ℕ → Ω → ℝ)
    (hL2 : ∀ i, i ≤ m → MemLp (U i) 2 P)
    (hadapt : ∀ i, i ≤ m → StronglyMeasurable[𝓖 (i + 1)] (U i))
    (hcentred : ∀ i, i ≤ m → P[U i | 𝓖 i] =ᵐ[P] (fun _ => 0)) :
    let V : ℕ → Ω → ℝ := fun i => if i ≤ m then U i else fun _ => 0
    (∀ i, MemLp (V i) 2 P) ∧
    (∀ i, StronglyMeasurable[𝓖 (i + 1)] (V i)) ∧
    (∀ i, P[V i | 𝓖 i] =ᵐ[P] (fun _ => 0)) := by sorry
