-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux20_finite_mark_eapprox_pullback
-- name    : AvramDividend.Classical.avram_redux20_finite_mark_eapprox_pullback
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:01:53.214169+00:00
-- url     : https://prove2.me/theorems/9bdca9d1-b42b-469d-aae8-ee99b82c8ab2
-- title:
--   Simple mark-loss approximations converge over finite physical jump times with multiplicity
-- statement:
--   On a finite set of actual physical jump times, the increasing simple approximation of a measurable nonnegative function of the jump mark converges at the level of total marked loss, even if the time-to-mark map has not separately been proved measurable. Different jump times with identical marks remain distinct and are counted with the correct multiplicity.
-- source:
--   Apply the already Proved monotone finite-sum supremum interchange 19c21901 to the simple approximants evaluated after an arbitrary mark map. Mathlib's monotone_eapprox and iSup_eapprox_apply prove the pointwise hypotheses for every marked time, independent of source-path measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux20_monotone_finite_mark_sum_iSup
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_redux20_finite_mark_eapprox_pullback
    {α β : Type*} [MeasurableSpace β]
    (S : Finset α) (mark : α → β)
    (g : β → ℝ≥0∞) (hg : Measurable g) :
    (⨆ n : ℕ, ∑ u ∈ S,
      MeasureTheory.SimpleFunc.eapprox g n (mark u)) =
      ∑ u ∈ S, g (mark u) := by sorry
