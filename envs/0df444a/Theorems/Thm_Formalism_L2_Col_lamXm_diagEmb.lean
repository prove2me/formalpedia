-- Prove2me | Theorems.Thm_Formalism_L2_Col_lamXm_diagEmb
-- name    : Formalism.L2.Col.lamXm_diagEmb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:34.768911+00:00
-- url     : https://prove2.me/theorems/56aee437-4707-4bbd-a2e3-64920620f4d3
-- title:
--   Col: lam Xm diag Emb
-- statement:
--   The Col construction uses the lam Xm diag Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L765-L777
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L765-L777

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

theorem Formalism.L2.Col.lamXm_diagEmb (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (r t m : ℕ) (g : ↥(HJ κ (r + m * t) r t m)) :
    lamXm ψ χ (r + m * t + 1) r t m
      ⟨diagEmb κ (Nat.le_succ (r + m * t)) g.1, ⟨diagEmb_mem_uniUT _ g.2, diagEmb_mem_fixCol _ le_rfl g.1⟩⟩ =
      lamJ ψ χ (r + m * t) r t m g := by sorry
