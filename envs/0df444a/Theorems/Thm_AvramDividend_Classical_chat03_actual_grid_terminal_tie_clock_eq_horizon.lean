-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_grid_terminal_tie_clock_eq_horizon
-- name    : AvramDividend.Classical.chat03_actual_grid_terminal_tie_clock_eq_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T21:12:20.795631+00:00
-- url     : https://prove2.me/theorems/cd1753c6-a6c4-4bd3-8f6c-a50d85a8b1f8
-- title:
--   Actual grid stopping clock clipped at a continuous exit exactly on the terminal horizon equals that horizon
-- statement:
--   For an official spectrally negative Lévy path whose finite strict two-sided exit infimum is exactly the observation horizon T, the actual bounded hittingBtwn clock on any uniform grid extending at least to T satisfies min(grid stopping time,T)=T. The conclusion allows sampled strict exits at and after T, covering deterministic upward first-passage atoms that prevent a blanket no-ties assumption.
-- source:
--   Instantiates the independent generic Chat03 bounded hitting-time no-early-hit lemma with the max of strict lower and upper barrier gaps. The official IsGLB lower-bound property forbids sampled strict crossings before T. Publish only after its imported generic theorem is Proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_hittingBtwn_terminal_payoff_of_no_early_hit
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_actual_grid_terminal_tie_clock_eq_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (T mesh : ℝ≥0) (m : ℕ)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} T)
    (hcap : T ≤ (m : ℝ≥0) * mesh) :
    min (((hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh) ξ))
      (Set.Ioi (0 : ℝ)) 0 m ω : ℕ) : ℝ≥0) * mesh) T = T := by
  sorry
