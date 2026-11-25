-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_kernel_line
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tail_kernel_line
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:30.651856+00:00
-- url     : https://prove2.me/theorems/6e67026f-e37b-4a41-a86f-04f678ab73f0
-- title:
--   Box Tail: tail kernel line
-- statement:
--   The Box Tail construction uses the tail kernel line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailKernel.lean#L89-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailKernel.lean#L89-L124

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

theorem Formalism.HermitianLattices.Ext.BoxTail.tail_kernel_line (σ T : ℝ) (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1 - 1 / 800) (hT : 0 ≤ T) :
    ∫ u in (-T)..T, 1 / ‖(σ : ℂ) + (u : ℂ) * I - 1‖ ≤ 4 * Real.log (1 + 800 * T) := by sorry
