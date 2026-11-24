-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_num
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tail_num
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:34.094794+00:00
-- url     : https://prove2.me/theorems/fb483689-e4e5-4daa-8559-fab69d1a102d
-- title:
--   Box Tail: tail num
-- statement:
--   The Box Tail construction uses the tail num property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailNum.lean#L76-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailNum.lean#L76-L137

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

theorem Formalism.HermitianLattices.Ext.BoxTail.tail_num (ε K : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : 0 ≤ K) : ∃ x₀ : ℝ, 3 ≤ x₀ ∧
    ∀ x Q : ℝ, x₀ ≤ x → 0 < Q → x ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ x ^ (ε / 4) →
      x * ((K * Real.log Q * (Real.log Q * (1 / x ^ 2) * (x ^ 400) ^ (1 - 1 / 400 + ε / 1600) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2))) ≤ x ^ ε := by sorry
