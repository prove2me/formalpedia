-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_strict_residual_jump_times_finite_of_finite_range
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_strict_residual_jump_times_finite_of_finite_range
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:22:57.148286+00:00
-- url     : https://prove2.me/theorems/dad57e67-afa6-4bc6-82ab-2ad39a1faa29
-- title:
--   Finite-range original BV Lévy residual has finitely many genuine strict residual jumps on a finite horizon
-- statement:
--   For the genuine original source BV spectrally negative Lévy process, assume the actual drift-residual path is known to have finite range on [0,T] on one P-almost-sure event. Then on a common P-full event the strictly positive-time source residual left-limit jumps are a finite set. Original source BV monotonicity is canonically Proved, and successive strict jumps inject into the finite set of actual postjump residual values. This is a source-specific finite-step jump-time interface, with the necessary finite-range event explicit; it does not assert a marked Poisson law or compensator.
-- source:
--   Canonical Proved source BV residual monotonicity f6cc1059-e8ca-403e-8d73-71a139d3dc4c. For u<v genuine strict residual jump times, Monotone.le_leftLim gives Y(u)≤leftLim Y(v)<Y(v). Thus jump-time ↦ source postjump residual value is injective into the finite actual-path range S. Pinned Mathlib Finite.of_injective and Set.toFinite provide finiteness, no extra sample space.

import Mathlib
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_strict_residual_jump_times_finite_of_finite_range
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (T : ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∃ S : Finset ℝ,
      ∀ t : ℝ≥0, t ≤ T →
        (t : ℝ) * X.drift - X.X t ω ∈ S) :
    ∀ᵐ ω ∂P,
      {t : ℝ≥0 |
        t ≤ T ∧ 0 < t ∧
          Function.leftLim
            (fun u : ℝ≥0 => (u : ℝ) * X.drift - X.X u ω) t <
            (t : ℝ) * X.drift - X.X t ω}.Finite := by sorry
