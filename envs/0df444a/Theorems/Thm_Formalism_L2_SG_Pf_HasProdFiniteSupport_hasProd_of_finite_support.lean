-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_of_finite_support
-- name    : Formalism.L2.SG.Pf.HasProdFiniteSupport.hasProd_of_finite_support
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:53:44.589432+00:00
-- url     : https://prove2.me/theorems/e1b3dbd7-7405-49eb-9100-8db86dfc2656
-- title:
--   Has Prod Finite Support: has Prod of finite support
-- statement:
--   The Has Prod Finite Support construction uses the has Prod of finite support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/HasProdFiniteSupport.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/HasProdFiniteSupport.lean#L52-L54

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_HasProdFiniteSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.HasProdFiniteSupport
open Filter Topology
variable {ι : Type*}

theorem Formalism.L2.SG.Pf.HasProdFiniteSupport.hasProd_of_finite_support {f : ι → ℝ} (s : Set ι) (hs : s.Finite) (h1 : ∀ i ∉ s, f i = 1) :
    HasProd f (∏ i ∈ hs.toFinset, f i) := by sorry
