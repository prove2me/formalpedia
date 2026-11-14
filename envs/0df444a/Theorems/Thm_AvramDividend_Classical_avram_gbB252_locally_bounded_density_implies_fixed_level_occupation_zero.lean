-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB252_locally_bounded_density_implies_fixed_level_occupation_zero
-- name    : AvramDividend.Classical.avram_gbB252_locally_bounded_density_implies_fixed_level_occupation_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:37:56.201093+00:00
-- url     : https://prove2.me/theorems/353d742a-962f-4add-9350-89dc38f07218
-- title:
--   Locally bounded compact spatial occupation density forces each fixed spatial level to have zero physical-time occupation
-- statement:
--   Given a genuine locally bounded compactly supported nonnegative spatial occupation-time density for a real path on any finite stopped physical-time horizon, every prescribed single spatial level has exactly zero Lebesgue occupation. The proof bounds shrinking-interval occupation by its length times the density's finite bound, then squeezes each singleton's occupation to zero. This is the deterministic result needed to derive adapted Gaussian fixed-level theorem B251 from local-time theorem B250.
-- source:
--   B250 adapted semimartingale local time to B251 fixed level occupation: deterministic spatial density bound plus width→0; results B242, B140, B170 already Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB252_locally_bounded_density_implies_fixed_level_occupation_zero
    (f : ℝ → ℝ) (n : ℕ) (ρ y : ℝ)
    (ℓ : ℝ → ℝ) (R : ℝ)
    (hLocal : ∀ z : ℝ,
      ∃ U ∈ 𝓝 z, Bornology.IsBounded (ℓ '' U))
    (hNonneg : ∀ z, 0 ≤ ℓ z)
    (hSupport : ∀ z, z ∉ Set.Icc (-R) R → ℓ z = 0)
    (hOccupation : ∀ a b : ℝ,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧
        f t ∈ Set.Ioo a b} =
      ∫⁻ z in Set.Ioo a b, ENNReal.ofReal (ℓ z) ∂volume) :
    volume {t : ℝ |
      0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧ f t = y} = 0 := by sorry
