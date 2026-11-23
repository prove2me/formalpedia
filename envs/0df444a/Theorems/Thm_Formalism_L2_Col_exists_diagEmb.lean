-- Prove2me | Theorems.Thm_Formalism_L2_Col_exists_diagEmb
-- name    : Formalism.L2.Col.exists_diagEmb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:13.269385+00:00
-- url     : https://prove2.me/theorems/7b20c16f-c61a-4a96-9211-c0eebd3f0abc
-- title:
--   Col: exists diag Emb
-- statement:
--   The Col construction uses the exists diag Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L111-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L111-L148

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

theorem Formalism.L2.Col.exists_diagEmb {s : ℕ} (M : GL (Fin (s + 1)) κ) (hc : M ∈ fixCol (s + 1) κ s)
    (hr : ∀ j : Fin (s + 1), j.val < s → (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) (Fin.last s) j = 0) :
    ∃ g : GL (Fin s) κ, diagEmb κ (Nat.le_succ s) g = M ∧
      ∀ i j : Fin s, (g : Matrix (Fin s) (Fin s) κ) i j = (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i.castSucc j.castSucc := by sorry
