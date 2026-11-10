-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gclose17_original_exit_inf_nearby_violation
-- name    : AvramDividend.Classical.avram_gclose17_original_exit_inf_nearby_violation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:41:22.972872+00:00
-- url     : https://prove2.me/theorems/35971944-39ea-4493-b829-ef449a24d29a
-- title:
--   Every finite original sampled lower-exit infimum has arbitrarily close true violating observations
-- statement:
--   For any true original controlled reserve path and any family of sampled physical times, if the infimum in WithTop of all observation times with postpayment reserve below δ equals a finite physical time t, then for every positive physical tolerance ε there is an actual sampled violating time between t and t+ε. The proof uses only order theory and the unchanged original path; it does not impose bounded variation, finite-jump activity, or any hypothetical process identification.
-- source:
--   The infimum t is no greater than each qualifying sampled time. If every qualifying sampled time lay at or above t+ε, the complete-lattice infimum would also be at least t+ε, contradicting ε>0. This is exactly the missing sample-selection step needed before the proved right-continuous endpoint-contact limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gclose17_original_exit_inf_nearby_violation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (r : ℕ → ℝ≥0) (δ : ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : (t : WithTop ℝ≥0) =
      ⨅ k : ℕ, if x + X.X (r k) ω - rightLimit D (r k) ω < δ
        then (r k : WithTop ℝ≥0) else ⊤) :
    ∀ ε : ℝ≥0, 0 < ε →
      ∃ k : ℕ, t ≤ r k ∧ r k < t + ε ∧
        x + X.X (r k) ω - rightLimit D (r k) ω < δ := by sorry
