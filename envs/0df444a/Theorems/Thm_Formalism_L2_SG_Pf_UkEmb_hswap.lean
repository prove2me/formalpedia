-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_UkEmb_hswap
-- name    : Formalism.L2.SG.Pf.UkEmb.hswap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:47:38.351972+00:00
-- url     : https://prove2.me/theorems/9be4c52c-94bc-4ef0-ac6a-fa5d08719787
-- title:
--   Uk Emb: hswap
-- statement:
--   The Uk Emb construction uses the hswap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/SmatUnitary.lean#L66-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/SmatUnitary.lean#L66-L72

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

theorem Formalism.L2.SG.Pf.UkEmb.hswap (J : Matrix (Fin n) (Fin n) ℂ) (hJh : Jᴴ = J) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (J *ᵥ y) = star (star y ⬝ᵥ (J *ᵥ x)) := by sorry
