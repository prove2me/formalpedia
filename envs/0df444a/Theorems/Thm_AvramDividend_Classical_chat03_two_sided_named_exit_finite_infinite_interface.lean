-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_two_sided_named_exit_finite_infinite_interface
-- name    : AvramDividend.Classical.chat03_two_sided_named_exit_finite_infinite_interface
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:16:25.060228+00:00
-- url     : https://prove2.me/theorems/a52ea59d-4ace-40ab-a710-1a993e9b4ae9
-- title:
--   Official strict upper and lower first-passage clocks: finite greatest lower bounds and infinity/no-exit equivalences
-- statement:
--   For the official named strict upper and lower first-passage clocks twoSidedExitUpTime and twoSidedExitDownTime of a spectrally negative Lévy process, prove the complete finite/infinity interface. Whenever the upward (respectively downward) clock is finite in ℝ≥0∞, its toNNReal is the greatest lower bound of all strict upward (respectively downward) witnessing nonnegative real times. The upward clock equals infinity exactly when no upward strict-crossing witness exists, and likewise for the downward clock. All four properties are derived from two independently Proved generic ENNReal indexed-infimum theorems, preserving the exact strict predicates and infinity semantics. No right-continuity of the filtration or killed q-scale martingale is assumed. This establishes the missing definitional bridge for reusing the Proved grid first-passage convergence theorems with the parent's exact clocks.
-- source:
--   Pinned Formalpedia Definitions.Def_AvramDividend_Classical_TwoSidedExit plus Proved Chat03 generic theorems finite_extended_infimum_isGLB UUID 9e18c0e5-9287-4efb-9f47-124d90a5a4ab and extended_infimum_is_top_iff_no_exit UUID 7ff7f7db-c9c8-41a7-a4ae-23610b3bd9f2, revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_finite_extended_infimum_isGLB
import Theorems.Thm_AvramDividend_Classical_chat03_extended_infimum_is_top_iff_no_exit

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_two_sided_named_exit_finite_infinite_interface
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (u d : ℝ) (ω : Ω) :
    (twoSidedExitUpTime X u ω ≠ ∞ →
      IsGLB {t : ℝ≥0 | u < X.X t ω}
        (twoSidedExitUpTime X u ω).toNNReal) ∧
    (twoSidedExitDownTime X d ω ≠ ∞ →
      IsGLB {t : ℝ≥0 | X.X t ω < d}
        (twoSidedExitDownTime X d ω).toNNReal) ∧
    (twoSidedExitUpTime X u ω = ∞ ↔
      ¬ ∃ t : ℝ≥0, u < X.X t ω) ∧
    (twoSidedExitDownTime X d ω = ∞ ↔
      ¬ ∃ t : ℝ≥0, X.X t ω < d) := by sorry
