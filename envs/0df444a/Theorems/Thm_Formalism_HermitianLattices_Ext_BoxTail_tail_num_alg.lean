-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_num_alg
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tail_num_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:29.283866+00:00
-- url     : https://prove2.me/theorems/acbed5db-2b5d-4738-b1fd-512e2c9b2562
-- title:
--   Box Tail: tail num alg
-- statement:
--   The Box Tail construction uses the tail num alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailNum.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailNum.lean#L15-L22

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

theorem Formalism.HermitianLattices.Ext.BoxTail.tail_num_alg (x Q K l a g : ℝ) (hx : 0 < x) (hQ : 0 < Q) :
    x * ((K * l * (l * (1 / x ^ 2) * (x ^ 399 * a) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * g / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2)))
      = K * l ^ 2 * a + K * (l * x ^ 403 / Q) + (x ^ 398 + 1) * g / x ^ 399 := by sorry
