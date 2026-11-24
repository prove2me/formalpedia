-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_norm_exp_sub_one_le_of_re_nonneg
-- name    : Formalism.HermitianLattices.Ext.BoxTail.norm_exp_sub_one_le_of_re_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:50.04242+00:00
-- url     : https://prove2.me/theorems/c75de383-53d8-472d-a067-1ec5dcc5273e
-- title:
--   Box Tail: norm exp sub one le of re nonneg
-- statement:
--   The Box Tail construction uses the norm exp sub one le of re nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailKernel.lean#L9-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailKernel.lean#L9-L25

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

theorem Formalism.HermitianLattices.Ext.BoxTail.norm_exp_sub_one_le_of_re_nonneg (u : ℂ) (hu : 0 ≤ u.re) :
    ‖Complex.exp u - 1‖ ≤ Real.exp u.re * ‖u‖ := by sorry
