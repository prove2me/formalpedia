-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_finite_reciprocal_cutoff_tsum_toReal_iSup
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_finite_reciprocal_cutoff_tsum_toReal_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:00:30.083187+00:00
-- url     : https://prove2.me/theorems/76b54ecd-bf34-4758-afc8-f602c50a1b3a
-- title:
--   Finite ENNReal jump total equals supremum of real-valued reciprocal-cutoff tsums
-- statement:
--   For any index type and nonnegative extended-real mass assignment with finite total, the real-valued full tsum equals the supremum of the real-valued reciprocal cutoff tsums. This supplies the exact no-Poisson limit conversion needed for original finite-variation left-jump change of variables.
-- source:
--   Apply Proved Avram P3-A reciprocal-cutoff ENNReal tsum equality 202efe84, pinned Mathlib ENNReal.toReal_iSup and ENNReal.tsum_le_tsum with the finite-total bound to justify each truncated tsum below top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_reciprocal_cutoff_tsum_eq_full

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- For finite total mass, real-valued reciprocal ENNReal cutoff totals increase
to the full real-valued mass, with no countability hypothesis on indices. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_finite_reciprocal_cutoff_tsum_toReal_iSup
    {α : Type*} (f : α → ℝ≥0∞) (hfinite : (∑' a : α, f a) < ⊤) :
    (⨆ n : ℕ, (∑' a : α,
      if (n : ℝ≥0∞)⁻¹ < f a then f a else 0).toReal) =
      (∑' a : α, f a).toReal := by sorry
