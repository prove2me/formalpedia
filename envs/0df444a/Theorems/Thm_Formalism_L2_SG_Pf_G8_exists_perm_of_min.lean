-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G8_exists_perm_of_min
-- name    : Formalism.L2.SG.Pf.G8.exists_perm_of_min
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:23:39.517032+00:00
-- url     : https://prove2.me/theorems/b319f024-1cd9-56d8-a819-59bfb5debfa8
-- title:
--   G8: exists perm of min
-- statement:
--   The G8 construction uses the exists perm of min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsPermOfMin.lean#L42-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsPermOfMin.lean#L42-L52

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_FibPNeZeroOfGenus
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IsomFixOfExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsPermOfMin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G8
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

theorem Formalism.L2.SG.Pf.G8.exists_perm_of_min {n : ℕ} (e e' : Fin n → ℕ) (H : ∀ j, ∑ i, min (e i) j = ∑ i, min (e' i) j) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, e' (σ i) = e i := by sorry
