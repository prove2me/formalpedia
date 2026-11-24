-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tc_log_bound
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tc_log_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:03.216268+00:00
-- url     : https://prove2.me/theorems/34a80613-3835-4634-8667-7600033184fe
-- title:
--   Box Tail: tc log bound
-- statement:
--   The Box Tail construction uses the tc log bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourB.lean#L261-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourB.lean#L261-L271

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailKernel
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailContourB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail

theorem Formalism.HermitianLattices.Ext.BoxTail.tc_log_bound (Q : ℝ) (hQ : 2 ≤ Q) : Real.log (1 + 800 * (Q / 2)) ≤ 10 * Real.log Q := by sorry
