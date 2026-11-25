-- Prove2me | Theorems.Thm_Formalism_L2_Col_sym_arith
-- name    : Formalism.L2.Col.sym_arith
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:50:52.16466+00:00
-- url     : https://prove2.me/theorems/0ce96546-6520-5644-9a65-51619df0f666
-- title:
--   Col: sym arith
-- statement:
--   The Col construction uses the sym arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L858-L872
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L858-L872

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
variable {n : ℕ} {κ : Type} [CommRing κ]

theorem Formalism.L2.Col.sym_arith (k s : ℕ) :
    (k + 2 * s + 1) * (k + 2 * s + 1 - 1) / 2 - k =
      ((k + 2 * s + 1) ^ 2 - (k + 1) ^ 2 - 2 * s) / 2 + k * (k - 1) / 2 := by sorry
