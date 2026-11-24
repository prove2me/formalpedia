-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_num_exp
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tail_num_exp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:51.310198+00:00
-- url     : https://prove2.me/theorems/ffadae9f-0b03-413b-b123-260172fac8ef
-- title:
--   Box Tail: tail num exp
-- statement:
--   The Box Tail construction uses the tail num exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailNum.lean#L56-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailNum.lean#L56-L74

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

theorem Formalism.HermitianLattices.Ext.BoxTail.tail_num_exp (ε K : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in Filter.atTop, K * (x ^ 404 * Real.exp (-(x ^ (ε / 6)))) ≤ 1 / 3 := by sorry
