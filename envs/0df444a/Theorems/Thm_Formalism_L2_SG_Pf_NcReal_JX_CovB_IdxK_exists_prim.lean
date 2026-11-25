-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_NcReal_JX_CovB_IdxK_exists_prim
-- name    : Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK.exists_prim
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:19.470899+00:00
-- url     : https://prove2.me/theorems/0d4ae303-71d4-464e-948e-ee8b09949b2e
-- title:
--   Idx K: exists prim
-- statement:
--   The Idx K construction uses the exists prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CovolIdxK.lean#L12-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CovolIdxK.lean#L12-L66

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CovolIdxK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcReal Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.Pf.NcReal.JX.CovB Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK.exists_prim {m : ℕ} (c : Fin m → 𝓞 K) (hc : c ≠ 0) (𝔭 : Ideal (𝓞 K)) (h𝔭 : 𝔭 ≠ ⊤) :
    ∃ t : K, (∀ i, ∃ o : 𝓞 K, (o : K) = t * (c i : K)) ∧ ∃ i, ∀ o : 𝓞 K, (o : K) = t * (c i : K) → o ∉ 𝔭 := by sorry
