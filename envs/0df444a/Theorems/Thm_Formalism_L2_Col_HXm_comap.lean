-- Prove2me | Theorems.Thm_Formalism_L2_Col_HXm_comap
-- name    : Formalism.L2.Col.HXm_comap
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:44:04.772949+00:00
-- url     : https://prove2.me/theorems/e326eb11-0fa7-49ed-9e3c-3b087e5d75da
-- title:
--   Col: HXm comap
-- statement:
--   The Col construction uses the HXm comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L188-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L188-L201

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
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]

theorem Formalism.L2.Col.HXm_comap (r t m : ℕ) :
    (HXm κ (r + m * t + 1) r t m).comap (diagEmb κ (Nat.le_succ (r + m * t))) = HJ κ (r + m * t) r t m := by sorry
