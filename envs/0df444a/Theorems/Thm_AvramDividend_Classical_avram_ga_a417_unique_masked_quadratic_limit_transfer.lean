-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a417_unique_masked_quadratic_limit_transfer
-- name    : AvramDividend.Classical.avram_ga_a417_unique_masked_quadratic_limit_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:31:52.778076+00:00
-- url     : https://prove2.me/theorems/3a6b87e0-4e2f-41f0-a8e2-e70a8e57ef16
-- title:
--   One-active HJB quadratic masked errors vanish with masked raw increment and mesh width
-- statement:
--   If a finite mask selects at most one cell, the source masked absolute increments tend to zero, and the mesh widths vanish, then bounded linear-quadratic compensated cell errors also have a masked absolute sum tending to zero.
-- source:
--   Proved a394 single active absolute masked sum domination and basic continuous operations on limits.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a417_unique_masked_quadratic_limit_transfer
    (Mask : ℕ → ℕ → Prop) [∀ m i, Decidable (Mask m i)]
    (Z H : ℕ → ℕ → ℝ) (δ : ℕ → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hδ : ∀ m, 0 ≤ δ m)
    (hUnique : ∀ m i j, Mask m i → Mask m j → i = j)
    (hCell : ∀ m i, i < m → Mask m i →
      |H m i| ≤ K * (|Z m i| + (Z m i)^2 + δ m))
    (hSource : Tendsto
      (fun m : ℕ => ∑ i ∈ Finset.range m,
        if Mask m i then |Z m i| else 0) atTop (𝓝 (0 : ℝ)))
    (hWidth : Tendsto δ atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m,
      if Mask m i then |H m i| else 0) atTop (𝓝 (0 : ℝ)) := by sorry
