-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_discounted_terminal_one_sided_modulus
-- name    : AvramDividend.Classical.avram_bva_a22_original_BV_discounted_terminal_one_sided_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:41:09.914047+00:00
-- url     : https://prove2.me/theorems/35c879d1-7389-4b3d-8f67-bc2aaf446f75
-- title:
--   Original BV discounted full-horizon terminal omission is eventually small on closed nonnegative reserve bands
-- statement:
--   For the authentic original bounded-variation Levy process and dividend strategy, assuming candidate monotonicity and a uniform continuity modulus on a closed nonnegative reserve band, the discounted full-horizon candidate increase beyond the last strict physical grid clock becomes arbitrarily small uniformly on original paths whenever both reserves stay inside the band and the horizon candidate is nonnegative. The proof uses the original last-cell one-sided reserve modulus and monotonic nonnegative discount factors. It includes the zero-reserve boundary and needs no finite jump activity or global generator L1. Spatial boundary localisation and compensated jump C1 source alignment remain separate tasks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_uniform_terminal_one_sided_modulus
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_BV_discounted_terminal_one_sided_modulus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q) (B : ℝ)
    (hmono : MonotoneOn w (Icc (0 : ℝ) B))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ Icc (0 : ℝ) B, ∀ z ∈ Icc (0 : ℝ) B,
      |z - y| < δ → |w z - w y| < ε)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop,
      ∀ᵐ ω ∂P,
        (x + X.X (u m (m + 1)) ω -
          rightLimit D (u m (m + 1)) ω) ∈ Icc (0 : ℝ) B →
        (x + X.X S ω - rightLimit D S ω) ∈ Icc (0 : ℝ) B →
        0 ≤ w (x + X.X S ω - rightLimit D S ω) →
        Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω) -
          Real.exp (-(q * (u m (m + 1) : ℝ))) *
            w (x + X.X (u m (m + 1)) ω -
              rightLimit D (u m (m + 1)) ω) ≤ ε := by sorry
