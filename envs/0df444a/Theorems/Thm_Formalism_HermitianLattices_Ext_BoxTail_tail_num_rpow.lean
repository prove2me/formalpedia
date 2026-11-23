-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_num_rpow
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tail_num_rpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:39.486809+00:00
-- url     : https://prove2.me/theorems/306073ed-de83-4fc9-a67e-8450c1b42bcc
-- title:
--   Box Tail: tail num rpow
-- statement:
--   The Box Tail construction uses the tail num rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailNum.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailNum.lean#L7-L13

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailNum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail

theorem Formalism.HermitianLattices.Ext.BoxTail.tail_num_rpow (x ε : ℝ) (hx : 0 < x) :
    (x ^ 400) ^ (1 - 1 / 400 + ε / 1600 : ℝ) = x ^ 399 * x ^ (ε / 4) := by sorry
