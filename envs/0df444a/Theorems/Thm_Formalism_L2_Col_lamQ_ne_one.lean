-- Prove2me | Theorems.Thm_Formalism_L2_Col_lamQ_ne_one
-- name    : Formalism.L2.Col.lamQ_ne_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:17.818034+00:00
-- url     : https://prove2.me/theorems/daf8df8b-7e9f-4292-adb0-efbed89909bf
-- title:
--   Col: lam Q ne one
-- statement:
--   The Col construction uses the lam Q ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L604-L614
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L604-L614

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

theorem Formalism.L2.Col.lamQ_ne_one {ξ : κˣ →* Kˣ} {a b : ℕ} (hb : 0 < b) (hn : a + b ≤ n) (hξ : ξ ≠ 1) : lamQ ξ n a b ≠ 1 := by sorry
