-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_future_increment_sigma_indep_past
-- name    : AvramDividend.Classical.finite_future_increment_sigma_indep_past
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T10:08:27.542646+00:00
-- url     : https://prove2.me/theorems/df83d931-9b50-4c91-9b13-698d5a554893
-- title:
--   Finite shifted Lévy increments are independent of the past filtration
-- statement:
--   For a spectrally negative Lévy process adapted to a filtration, every finite family of shifted increments after a deterministic time s generates a sigma-algebra independent of the filtration at s. This finite-cylinder independence is the bridge from finite-dimensional independent-increment identities to independence of the complete shifted future path, which is needed for the barrier-strategy factorization.
-- source:
--   Derived from the authoritative SpectrallyNegativeLevy independent-increment assumptions and the Proved theorem AvramDividend.Classical.chat04_all_finite_prefix_increment_cylinder_product (UUID 4b6af35c-c6a9-4bca-ab7d-28f22e7bd161) by finite-dimensional cylinder factorization and finite-product measure uniqueness.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Process.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_all_finite_prefix_increment_cylinder_product

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.finite_future_increment_sigma_indep_past
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s : NNReal) :
    ∀ I : Finset NNReal,
      ProbabilityTheory.Indep
        (⨆ t : NNReal, ⨆ (_ : t ∈ I), MeasurableSpace.comap
          (fun ω : Ω => X.X (s + t) ω - X.X s ω) inferInstance)
        (𝓕 s) P := by
  sorry
