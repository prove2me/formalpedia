-- Prove2me | Theorems.Thm_Formalism_L2_Col_detChar_dGL
-- name    : Formalism.L2.Col.detChar_dGL
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:10:24.525168+00:00
-- url     : https://prove2.me/theorems/0c4c5bab-0d83-47d7-bcc9-797541779033
-- title:
--   Col: det Char d GL
-- statement:
--   The Col construction uses the det Char d GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L556-L563
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L556-L563

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

theorem Formalism.L2.Col.detChar_dGL (χ : ℕ → κˣ →* Kˣ) {a : ℕ} (bl : List ℕ) (i₀ : Fin n) {s : ℕ} (hs : s < bl.length)
    (h₀ : coarse a bl i₀.val = s + 1) (u : κˣ) : detChar χ n a bl ⟨dGL i₀ u, dGL_mem_btG _ i₀ u⟩ = χ s u := by sorry
