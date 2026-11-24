-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_box_log
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tail_box_log
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:46.98672+00:00
-- url     : https://prove2.me/theorems/64e223e2-1fe5-4353-9396-cb0e7ba6a4f9
-- title:
--   Box Tail: tail box log
-- statement:
--   The Box Tail construction uses the tail box log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailBox.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailBox.lean#L13-L24

import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LandauLemmaLfunctionZeros
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LandauLocal3
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LRight
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailBox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail

theorem Formalism.HermitianLattices.Ext.BoxTail.tail_box_log {n t Q : ℝ} (hn : 1 ≤ n) (hQ : 2 ≤ Q) (hnQ : n ≤ Q) (ht : |t| ≤ Q - 1) :
    Real.log (n * (|t| + 2)) ≤ 3 * Real.log Q := by sorry
