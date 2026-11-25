-- Prove2me | Theorems.Thm_Formalism_L2_Col_index_HPsym
-- name    : Formalism.L2.Col.index_HPsym
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:44:39.755185+00:00
-- url     : https://prove2.me/theorems/668f96c8-7e47-4ebf-ae51-acfd25bdf08c
-- title:
--   Col: index HPsym
-- statement:
--   The Col construction uses the index HPsym property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L876-L921
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L876-L921

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col

theorem Formalism.L2.Col.index_HPsym (F : Type) [Field F] [Fintype F] [DecidableEq F] (k m : ℕ) (hm : 2 ≤ m) (hev : Even m)
    (h3 : 3 ≤ Fintype.card F) :
    ∃ θ : ℝ, 1 / 2 ≤ θ ∧ θ ≤ 1 ∧ ((HPsym F (k + m - 1) k (m / 2 - 1)).index : ℝ) =
      (Fintype.card F : ℝ) ^ (((k + m - 1) ^ 2 + 3 * k + 1 + 2 * (m / 2 - 1)) / 2) * θ := by sorry
