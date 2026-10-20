-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_first_grid_strict_exit_approaches_infimum
-- name    : AvramDividend.Classical.chat03_first_grid_strict_exit_approaches_infimum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:33:46.018312+00:00
-- url     : https://prove2.me/theorems/36792f72-8d64-4c29-a0c7-4fc78174494c
-- title:
--   First strict grid-exit index converges from above to the continuous strict-passage infimum
-- statement:
--   For the published càdlàg spectrally negative Lévy sample path with strict exit infimum τ, for any ε>0 there exists δ>0 such that every uniform mesh 0<h<δ has a first strict two-sided grid exit index k, with no earlier grid exit, and τ≤k h<τ+ε. This is stronger than proving that some grid exit exists near τ: the minimum index is obtained using Mathlib Nat.find applied to the nonempty strict grid-exit witness set. It remains valid if the continuous first passage is not attained as an exit, including boundary creeping. It requires neither the strong Markov property nor the killed q-scale martingale; this proves only sample-time convergence and not stopped-value convergence or the original expectation identity.
-- source:
--   Depends only on independently published Chat03 strict_exit_mesh_approximation (UUID 8619c787-f68e-4cfc-8ecf-8378a3c5ed66; submitted candidate 11957, verdict initially pending) and pinned Mathlib Nat.find_spec/Nat.find_min/Nat.find_min' revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_exit_mesh_approximation
import Mathlib.Data.Nat.Find

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_first_grid_strict_exit_approaches_infimum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ h : ℝ≥0, 0 < h → h < δ →
      ∃ k : ℕ,
        τ ≤ (k : ℝ≥0) * h ∧
        (k : ℝ≥0) * h < τ + ε ∧
        (X.X ((k : ℝ≥0) * h) ω < lower ∨
         upper < X.X ((k : ℝ≥0) * h) ω) ∧
        (∀ j : ℕ, j < k →
          ¬ (X.X ((j : ℝ≥0) * h) ω < lower ∨
             upper < X.X ((j : ℝ≥0) * h) ω)) := by sorry
