-- Prove2me | Theorems.Thm_Formalism_L2_Col_chiSymF_apply
-- name    : Formalism.L2.Col.chiSymF_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:16.903328+00:00
-- url     : https://prove2.me/theorems/ba6452a5-5e4d-4c7c-bb0d-06b91af77c50
-- title:
--   Col: chi Sym F apply
-- statement:
--   The Col construction uses the chi Sym F apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGSym.lean#L76-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGSym.lean#L76-L77

import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGSym
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.Col
variable (κ : Type) [CommRing κ]
variable {κ}
variable (κ)
variable {κ}
variable {K : Type} [Field K]

theorem Formalism.L2.Col.chiSymF_apply (ψ : AddChar κ K) (n k rS : ℕ) (M : ↥(HPsymF κ n k rS)) :
    chiSymF ψ n k rS M = chiSym ψ n k rS ⟨toSymOrd κ n k rS M.1, M.2⟩ := by sorry
