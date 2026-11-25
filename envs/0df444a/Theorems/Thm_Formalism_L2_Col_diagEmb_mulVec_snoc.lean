-- Prove2me | Theorems.Thm_Formalism_L2_Col_diagEmb_mulVec_snoc
-- name    : Formalism.L2.Col.diagEmb_mulVec_snoc
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:52:32.340829+00:00
-- url     : https://prove2.me/theorems/ed596914-dae1-5b3e-a8a5-e39f46f92fbd
-- title:
--   Col: diag Emb mul Vec snoc
-- statement:
--   The Col construction uses the diag Emb mul Vec snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L971-L978
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L971-L978

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
variable {κ : Type} [CommRing κ] {K : Type} [Field K]

theorem Formalism.L2.Col.diagEmb_mulVec_snoc {n : ℕ} (h : GL (Fin n) κ) (v : Fin n → κ) (c : κ) :
    (diagEmb κ (Nat.le_succ n) h).1.mulVec (Fin.snoc (α := fun _ => κ) v c) =
      Fin.snoc (α := fun _ => κ) (h.1.mulVec v) c := by sorry
