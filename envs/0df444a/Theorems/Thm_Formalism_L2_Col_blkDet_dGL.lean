-- Prove2me | Theorems.Thm_Formalism_L2_Col_blkDet_dGL
-- name    : Formalism.L2.Col.blkDet_dGL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:02.28605+00:00
-- url     : https://prove2.me/theorems/15e06a8f-6c1d-41e3-89fc-2a660049da29
-- title:
--   Col: blk Det d GL
-- statement:
--   The Col construction uses the blk Det d GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L518-L539
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L518-L539

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

theorem Formalism.L2.Col.blkDet_dGL (β : ℕ → ℕ) (c : ℕ) (i₀ : Fin n) (u : κˣ) :
    blkDet n κ β c ⟨dGL i₀ u, dGL_mem_btG β i₀ u⟩ = if β i₀.val = c then u else 1 := by sorry
