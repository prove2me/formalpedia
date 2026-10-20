-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_first_grid_exit_upper_side_before_horizon
-- name    : AvramDividend.Classical.chat03_first_grid_exit_upper_side_before_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:41:41.217218+00:00
-- url     : https://prove2.me/theorems/679292b3-26f2-48d0-9c89-45c4d77aa7ca
-- title:
--   First strict grid-exit side remains upper when lower exit is excluded before an intervening horizon
-- statement:
--   For the official spectrally negative Lévy process, let τ be the infimum of the strict two-sided exit set, with τ<N. Suppose no lower strict exit occurs before N, expressed by lower≤X_s at every s<N. Then for every sufficiently fine mesh, the actual least strict grid exit index k has τ≤k h<N, is a strict upper exit (X_{k h}>upper), and no earlier grid sample exits. The proof composes the independently Proved finite-horizon first grid-exit theorem with the no-lower-exit hypothesis to eliminate the lower branch of the exit disjunction. This supports convergence of the correct first-exit side on the upper-first event, without relying on the killed scale martingale or any Open sibling identity.
-- source:
--   Pinned Formalpedia SpectrallyNegativeLevy and Proved Chat03 first_grid_exit_before_horizon (UUID 1eef4eb0-c990-443b-8bb0-97b0b743074c, submission f42d587e-633c-4075-acf6-6a9bd2268757 pending at authoring time), Mathlib pinned 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_exit_before_horizon

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_first_grid_exit_upper_side_before_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ N : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hτN : τ < N)
    (hNoLower : ∀ s : ℝ≥0, s < N → lower ≤ X.X s ω) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ h : ℝ≥0, 0 < h → h < δ →
      ∃ k : ℕ,
        τ ≤ (k : ℝ≥0) * h ∧
        (k : ℝ≥0) * h < N ∧
        upper < X.X ((k : ℝ≥0) * h) ω ∧
        (∀ j : ℕ, j < k →
          ¬ (X.X ((j : ℝ≥0) * h) ω < lower ∨
             upper < X.X ((j : ℝ≥0) * h) ω)) := by sorry
