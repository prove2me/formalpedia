-- Prove2me | Theorems.Thm_Formalism_L2_Col_dGL_mem_HK
-- name    : Formalism.L2.Col.dGL_mem_HK
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:51:07.596692+00:00
-- url     : https://prove2.me/theorems/a717da8f-9f61-413a-87fe-4ee1236b4d26
-- title:
--   Col: d GL mem HK
-- statement:
--   The Col construction uses the d GL mem HK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L541-L554
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L541-L554

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

theorem Formalism.L2.Col.dGL_mem_HK {r : ℕ} (bl : List ℕ) (i₀ : Fin n) (h₀ : r ≤ i₀.val) (u : κˣ) : dGL i₀ u ∈ HK n κ r bl := by sorry
