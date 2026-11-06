-- Prove2me | solution 1 for le_of_eventually_nhdsWithin
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:24:26.246016+00:00
-- url     : https://prove2.me/submissions/202c9a40-4ce4-4873-9983-da9a40eab1ed

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

open Filter Set
open scoped Topology

theorem solution {a b : ℝ} (h : ∀ᶠ c in 𝓝[>] b, a ≤ c) : a ≤ b := by
  by_contra hab
  have hba : b < a := lt_of_not_ge hab
  have hlt : ∀ᶠ c in 𝓝[>] b, c < a :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hba)
  obtain ⟨c, hac, hca⟩ := (h.and hlt).exists
  exact (not_lt_of_ge hac) hca
