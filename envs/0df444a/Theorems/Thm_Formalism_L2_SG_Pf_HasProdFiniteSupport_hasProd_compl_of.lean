-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_compl_of
-- name    : Formalism.L2.SG.Pf.HasProdFiniteSupport.hasProd_compl_of
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:47:21.162443+00:00
-- url     : https://prove2.me/theorems/91d9a4ab-4085-4db2-aa95-d455a5bf451e
-- title:
--   Has Prod Finite Support: has Prod compl of
-- statement:
--   The Has Prod Finite Support construction uses the has Prod compl of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/HasProdFiniteSupport.lean#L35-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/HasProdFiniteSupport.lean#L35-L50

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

theorem Formalism.L2.SG.Pf.HasProdFiniteSupport.hasProd_compl_of (P : ι → Prop) [DecidablePred P] [Fintype {i // P i}] {f : ι → ℝ} {a : ℝ}
    (h : HasProd f a) (hf : ∀ i, P i → f i ≠ 0) :
    HasProd (fun i : {i // ¬ P i} => f i) (a * (∏ i : {i // P i}, f i)⁻¹) := by sorry
