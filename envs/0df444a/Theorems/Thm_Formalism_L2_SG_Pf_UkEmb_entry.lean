-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_UkEmb_entry
-- name    : Formalism.L2.SG.Pf.UkEmb.entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:17:49.279803+00:00
-- url     : https://prove2.me/theorems/6216ff88-ac59-47e8-bc12-d11124f43804
-- title:
--   Uk Emb: entry
-- statement:
--   The Uk Emb construction uses the entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/SmatUnitary.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/SmatUnitary.lean#L17-L24

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_SmatUnitary
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.UkEmb
variable {n k : ℕ}

theorem Formalism.L2.SG.Pf.UkEmb.entry (wf : Fin k → Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (a b : Fin k) :
    ((Wm wf)ᴴ * M * Wm wf) a b = star (wf a) ⬝ᵥ (M *ᵥ wf b) := by sorry
