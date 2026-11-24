-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_boxCountHyp_outright
-- name    : Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.boxCountHyp_outright
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:18.804161+00:00
-- url     : https://prove2.me/theorems/6e224aae-e188-43bf-9912-034f28bd3d13
-- title:
--   Primitive Character Casts: box Count Hyp outright
-- statement:
--   The Primitive Character Casts construction uses the box Count Hyp outright property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountOut.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountOut.lean#L6-L7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZAll
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountFinal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountOut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts

theorem Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.boxCountHyp_outright : ∃ C : ℝ, Formalism.HermitianLattices.ZeroFreeRegionGL2.BoxCountHyp C := by sorry
