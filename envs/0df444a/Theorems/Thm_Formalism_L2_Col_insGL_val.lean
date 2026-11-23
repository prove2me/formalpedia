-- Prove2me | Theorems.Thm_Formalism_L2_Col_insGL_val
-- name    : Formalism.L2.Col.insGL_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:44.653903+00:00
-- url     : https://prove2.me/theorems/a98c7398-d828-42c4-ba5d-13cf95d6b196
-- title:
--   Col: ins GL val
-- statement:
--   The Col construction uses the ins GL val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGSym.lean#L184-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGSym.lean#L184-L186

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

theorem Formalism.L2.Col.insGL_val (N c k N' : ℕ) (hk : k ≤ N) (hN : N' = N + c) (A : GL (Fin N) κ) (a b : Fin N') :
    ((insGL κ N c k N' hk hN A : GL (Fin N') κ) : Matrix (Fin N') (Fin N') κ) a b =
      Matrix.fromBlocks (A : Matrix (Fin N) (Fin N) κ) 0 0 1 (insEquiv N c k N' hk hN a) (insEquiv N c k N' hk hN b) := by sorry
