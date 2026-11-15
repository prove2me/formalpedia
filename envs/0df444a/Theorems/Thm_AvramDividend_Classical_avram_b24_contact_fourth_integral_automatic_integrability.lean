-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_contact_fourth_integral_automatic_integrability
-- name    : AvramDividend.Classical.avram_b24_contact_fourth_integral_automatic_integrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:45:58.737786+00:00
-- url     : https://prove2.me/theorems/88385f5a-9501-4b87-9c39-eef615008efd
-- title:
--   Original measurable stopped ruin-contact fourth moment integrable automatically and dominated by unconditional cells
-- statement:
--   From measurability of the ruin-clipped stop σ and each original Gaussian or compensated-mark source cell increment V_i, and integrability of their fourth powers on a finite ordered separated grid, automatically derive integrability of the fourth power of the single terminal-contact mesh sum and an upper bound on its expected fourth moment by the sum of unconditional cell fourth moments. This eliminates the separate contact-integrability assumption while keeping actual source and the strict-left/inclusive-right stopping interval.
-- source:
--   Proved B24 contact fourth moment pointwise and Bochner integral comparison; measurable finite indicator-sums.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_contact_fourth_L1_from_cell_fourth_moments
import Theorems.Thm_AvramDividend_Classical_avram_b24_ruincontact_mesh_fourth_moment_pathwise_dominance
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_contact_fourth_integral_automatic_integrability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (S : Finset ℕ) (a b : ℕ → ℝ≥0) (σ : Ω → ℝ≥0)
    (V : ℕ → Ω → ℝ)
    (hSep : ∀ i j, i ∈ S → j ∈ S → i < j → b i ≤ a j)
    (hσM : Measurable σ)
    (hVM : ∀ i ∈ S, Measurable (V i))
    (hVI : ∀ i ∈ S, Integrable (fun ω => ‖V i ω‖ ^ 4) P) :
    Integrable (fun ω =>
      ‖∑ i ∈ S.filter (fun i => a i < σ ω ∧ σ ω ≤ b i), V i ω‖ ^ 4) P ∧
    (∫ ω, ‖∑ i ∈ S.filter (fun i => a i < σ ω ∧ σ ω ≤ b i),
      V i ω‖ ^ 4 ∂P) ≤
      ∑ i ∈ S, ∫ ω, ‖V i ω‖ ^ 4 ∂P := by sorry
