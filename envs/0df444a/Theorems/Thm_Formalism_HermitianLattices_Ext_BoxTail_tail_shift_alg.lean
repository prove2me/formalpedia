-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_shift_alg
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tail_shift_alg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:43.521193+00:00
-- url     : https://prove2.me/theorems/8cf5c9c0-4cff-42b2-9563-79dc99127504
-- title:
--   Box Tail: tail shift alg
-- statement:
--   The Box Tail construction uses the tail shift alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourA.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourA.lean#L11-L18

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_RectShiftChi
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_IntegralEqIntervalIntegralAddCompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailContourA
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

theorem Formalism.HermitianLattices.Ext.BoxTail.tail_shift_alg (S R V0 V1 E a b : ℂ) (hS : S = (1 / (2 * Real.pi) : ℂ) * (V0 + E))
    (hrect : a - b + I * V0 - I * V1 = 2 * Real.pi * I * R) :
    (2 * Real.pi : ℂ) * (S - R) = E + I * (a - b) + V1 := by sorry
