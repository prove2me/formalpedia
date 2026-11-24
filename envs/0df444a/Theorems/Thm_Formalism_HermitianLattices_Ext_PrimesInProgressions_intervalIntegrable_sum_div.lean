-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_intervalIntegrable_sum_div
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.intervalIntegrable_sum_div
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:34.152915+00:00
-- url     : https://prove2.me/theorems/49c0aa2f-0413-4272-aab7-5d0a2597c3e7
-- title:
--   Primes In Progressions: interval Integrable sum div
-- statement:
--   The Primes In Progressions construction uses the interval Integrable sum div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiB.lean#L35-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiB.lean#L35-L66

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.intervalIntegrable_sum_div (c : ℕ → ℝ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (∑ n ∈ Icc 0 ⌊t⌋₊, c n) / (t * Real.log t ^ 2)) MeasureTheory.volume a b := by sorry
