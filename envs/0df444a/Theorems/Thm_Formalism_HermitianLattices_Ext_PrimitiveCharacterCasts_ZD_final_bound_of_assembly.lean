-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_final_bound_of_assembly
-- name    : Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.final_bound_of_assembly
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:57.765504+00:00
-- url     : https://prove2.me/theorems/bf7476d7-7ef4-47b1-8758-5e9c8d232f64
-- title:
--   ZD: final bound of assembly
-- statement:
--   The ZD construction uses the final bound of assembly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZFinal.lean#L10-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZFinal.lean#L10-L129

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZFinal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
attribute [local irreducible] q0 pY pJ pN

theorem Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.final_bound_of_assembly : FinalOf := by sorry
