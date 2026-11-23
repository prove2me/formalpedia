-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_num_third
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tail_num_third
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:34.93191+00:00
-- url     : https://prove2.me/theorems/0262c9bd-6307-425d-9526-d07eb7cc6047
-- title:
--   Box Tail: tail num third
-- statement:
--   The Box Tail construction uses the tail num third property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailNum.lean#L24-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailNum.lean#L24-L54

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

theorem Formalism.HermitianLattices.Ext.BoxTail.tail_num_third (x : ℝ) (hx : 3 ≤ x) :
    (x ^ 398 + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 399 ≤ 802 := by sorry
