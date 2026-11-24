-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tc_norm_comb
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tc_norm_comb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:38.042724+00:00
-- url     : https://prove2.me/theorems/dbf93d85-e77b-41bd-aa2b-5f50d19536b6
-- title:
--   Box Tail: tc norm comb
-- statement:
--   The Box Tail construction uses the tc norm comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourB.lean#L246-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourB.lean#L246-L259

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

theorem Formalism.HermitianLattices.Ext.BoxTail.tc_norm_comb (E1 E0 a1 b1 a0 b0 V1 V0 : ℂ) :
    ‖(E1 + I * (a1 - b1) + V1) - (E0 + I * (a0 - b0) + V0)‖ ≤
      ‖E1‖ + ‖E0‖ + ‖a1‖ + ‖b1‖ + ‖a0‖ + ‖b0‖ + ‖V1 - V0‖ := by sorry
