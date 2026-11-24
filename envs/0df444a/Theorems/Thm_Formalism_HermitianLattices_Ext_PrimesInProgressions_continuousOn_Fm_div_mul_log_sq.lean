-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_continuousOn_Fm_div_mul_log_sq
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.continuousOn_Fm_div_mul_log_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:53:25.597607+00:00
-- url     : https://prove2.me/theorems/52c21006-49dc-41c2-a0fb-055c0399d172
-- title:
--   Primes In Progressions: continuous On Fm div mul log sq
-- statement:
--   The Primes In Progressions construction uses the continuous On Fm div mul log sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiB.lean#L111-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiB.lean#L111-L126

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.continuousOn_Fm_div_mul_log_sq (K θ β : ℝ) {a b : ℝ} (ha : 2 ≤ a) :
    ContinuousOn (fun t => Fm K θ β t / (t * Real.log t ^ 2)) (Set.Icc a b) := by sorry
