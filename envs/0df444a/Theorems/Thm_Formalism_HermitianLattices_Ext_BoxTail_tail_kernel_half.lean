-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_kernel_half
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tail_kernel_half
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:44.223859+00:00
-- url     : https://prove2.me/theorems/8c724e0a-aece-40b0-9968-d174a137b910
-- title:
--   Box Tail: tail kernel half
-- statement:
--   The Box Tail construction uses the tail kernel half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailKernel.lean#L78-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailKernel.lean#L78-L87

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailKernel
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

theorem Formalism.HermitianLattices.Ext.BoxTail.tail_kernel_half (T : ℝ) (hT : 0 ≤ T) :
    ∫ u in (0 : ℝ)..T, 2 / (1 / 800 + u) = 2 * Real.log (1 + 800 * T) := by sorry
