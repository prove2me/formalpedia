-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_kernel_cpow
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tail_kernel_cpow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:15.843078+00:00
-- url     : https://prove2.me/theorems/e19dc13f-76e0-4edb-b942-c22ffd0a7b61
-- title:
--   Box Tail: tail kernel cpow
-- statement:
--   The Box Tail construction uses the tail kernel cpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailKernel.lean#L27-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailKernel.lean#L27-L64

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

theorem Formalism.HermitianLattices.Ext.BoxTail.tail_kernel_cpow (y η : ℝ) (hy : 0 < y) (hη : 0 ≤ η) (hη1 : η ≤ 1) (w : ℂ) (hw0 : 0 ≤ w.re)
    (hw2 : w.re ≤ 2) :
    ‖((y * (1 + η) : ℝ) : ℂ) ^ w - (y : ℂ) ^ w‖ ≤ 4 * η * ‖w‖ * y ^ w.re := by sorry
