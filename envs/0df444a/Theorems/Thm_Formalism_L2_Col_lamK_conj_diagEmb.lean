-- Prove2me | Theorems.Thm_Formalism_L2_Col_lamK_conj_diagEmb
-- name    : Formalism.L2.Col.lamK_conj_diagEmb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:41.629797+00:00
-- url     : https://prove2.me/theorems/101b2bb7-601d-4347-a4d6-c7528ceea404
-- title:
--   Col: lam K conj diag Emb
-- statement:
--   The Col construction uses the lam K conj diag Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L639-L657
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L639-L657

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

theorem Formalism.L2.Col.lamK_conj_diagEmb (χ : ℕ → κˣ →* Kˣ) {r : ℕ} (h : r ≤ n) {bl : List ℕ} (g : GL (Fin r) κ) (M : ↥(HK n κ r bl)) :
    lamK χ n r bl ⟨diagEmb κ h g * M.1 * (diagEmb κ h g)⁻¹, HK_conj_diagEmb h g M.2⟩ = lamK χ n r bl M := by sorry
