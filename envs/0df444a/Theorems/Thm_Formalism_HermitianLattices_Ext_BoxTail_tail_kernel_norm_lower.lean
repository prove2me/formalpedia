-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_kernel_norm_lower
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tail_kernel_norm_lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:43.895231+00:00
-- url     : https://prove2.me/theorems/faf8bcc1-180c-4a54-b9cc-f5976a97e966
-- title:
--   Box Tail: tail kernel norm lower
-- statement:
--   The Box Tail construction uses the tail kernel norm lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailKernel.lean#L66-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailKernel.lean#L66-L76

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

theorem Formalism.HermitianLattices.Ext.BoxTail.tail_kernel_norm_lower (σ u : ℝ) (hσ1 : σ ≤ 1 - 1 / 800) :
    (1 / 800 + |u|) / 2 ≤ ‖(σ : ℂ) + (u : ℂ) * I - 1‖ := by sorry
