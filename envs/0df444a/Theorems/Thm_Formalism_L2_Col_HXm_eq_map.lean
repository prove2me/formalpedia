-- Prove2me | Theorems.Thm_Formalism_L2_Col_HXm_eq_map
-- name    : Formalism.L2.Col.HXm_eq_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:56.010273+00:00
-- url     : https://prove2.me/theorems/46677deb-232e-4ed6-9a0f-a67b739f63c7
-- title:
--   Col: HXm eq map
-- statement:
--   The Col construction uses the HXm eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L150-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L150-L186

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

theorem Formalism.L2.Col.HXm_eq_map (r t m : ℕ) :
    HXm κ (r + m * t + 1) r t m = (HJ κ (r + m * t) r t m).map (diagEmb κ (Nat.le_succ (r + m * t))) := by sorry
