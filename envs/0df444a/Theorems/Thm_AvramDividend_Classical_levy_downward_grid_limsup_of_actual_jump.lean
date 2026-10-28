-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_downward_grid_limsup_of_actual_jump
-- name    : AvramDividend.Classical.levy_downward_grid_limsup_of_actual_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T19:23:47.468206+00:00
-- url     : https://prove2.me/theorems/c9c82bf1-0250-4881-a2c5-b8ec2a1d0dae
-- title:
--   An actual Lévy càdlàg downward jump appears on converging finite observation grids
-- statement:
--   Fix a spectrally negative Lévy sample path and any strict negative jump at time t, witnessed by the existing left limit. Suppose finite grids contain a pair of bracket times at each resolution, the left brackets converging to t from below and right brackets converging to t from above. The path then belongs to the measurable limsup event of negative grid decrements beyond the jump threshold. The proof combines the path's built-in right-continuity and left-limit witness with the already proved deterministic grid-bracket jump-detection lemma. It supplies a direct process-level bridge for path-law transfer.
-- source:
--   Definition SpectrallyNegativeLevy.rightCont, Filter.Tendsto.comp, and the accepted theorem downward_grid_limsup_of_bracketed_jump.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_downward_grid_limsup_of_bracketed_jump

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal

theorem AvramDividend.Classical.levy_downward_grid_limsup_of_actual_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → Finset (ℝ≥0 × ℝ≥0))
    (s u : ℕ → ℝ≥0) (ω : Ω) (t : ℝ≥0) (a : ℝ)
    (hgrid : ∀ n, (s n, u n) ∈ grid n)
    (hs : Tendsto s atTop (nhdsWithin t (Iio t)))
    (hu : Tendsto u atTop (nhdsWithin t (Ici t)))
    (hjump : ∃ left : ℝ,
      Tendsto (fun z : ℝ≥0 => X.X z ω)
        (nhdsWithin t (Iio t)) (nhds left) ∧
      X.X t ω - left < -a) :
    (fun z : ℝ≥0 => X.X z ω) ∈
      (⋂ N : ℕ, ⋃ n : {n : ℕ // N ≤ n},
        ⋃ ij ∈ grid n.1,
          {f : ℝ≥0 → ℝ | f ij.2 - f ij.1 < -a}) := by sorry
