-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_UkEmb_smat_unitary
-- name    : Formalism.L2.SG.Pf.UkEmb.smat_unitary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:17:35.929171+00:00
-- url     : https://prove2.me/theorems/19583d6d-6cf9-4b21-b7b2-d3f1a692753b
-- title:
--   Uk Emb: smat unitary
-- statement:
--   The Uk Emb construction uses the smat unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/SmatUnitary.lean#L83-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/SmatUnitary.lean#L83-L87

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
variable (J : Matrix (Fin n) (Fin n) ℂ) (wf : Fin k → Fin n → ℂ)
  (hon : ∀ a b, star (wf a) ⬝ᵥ (J *ᵥ wf b) = if a = b then 1 else 0)
include hon

theorem Formalism.L2.SG.Pf.UkEmb.smat_unitary (hJh : Jᴴ = J) (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ * G = 1) :
    (smat J wf G)ᴴ * J * smat J wf G = J := by sorry
