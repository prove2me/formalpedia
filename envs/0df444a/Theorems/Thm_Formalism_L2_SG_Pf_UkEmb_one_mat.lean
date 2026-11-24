-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_UkEmb_one_mat
-- name    : Formalism.L2.SG.Pf.UkEmb.one_mat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:08.864868+00:00
-- url     : https://prove2.me/theorems/b0fda2fb-6224-4e54-a85a-2a6054c7d9de
-- title:
--   Uk Emb: one mat
-- statement:
--   The Uk Emb construction uses the one mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/SmatUnitary.lean#L109-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/SmatUnitary.lean#L109-L111

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

theorem Formalism.L2.SG.Pf.UkEmb.one_mat (a b : Fin k) : star (wf a) ⬝ᵥ (J *ᵥ ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ wf b)) =
    (1 : Matrix (Fin k) (Fin k) ℂ) a b := by sorry
