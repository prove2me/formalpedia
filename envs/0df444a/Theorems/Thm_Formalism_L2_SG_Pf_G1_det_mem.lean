-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G1_det_mem
-- name    : Formalism.L2.SG.Pf.G1.det_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:45.449189+00:00
-- url     : https://prove2.me/theorems/b2d1e0a6-d5c4-4bba-b465-89de0f868e01
-- title:
--   G1: det mem
-- statement:
--   The G1 construction uses the det mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsOrthGen.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsOrthGen.lean#L12-L20

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTuple
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsOrthGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G1
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K}

theorem Formalism.L2.SG.Pf.G1.det_mem {h : V →ₗ⋆[K] V →ₗ[K] K} {n : ℕ} (x : Fin n → V) (hx : ∀ i j, h (x i) (x j) ∈ S) :
    (U0.gram h x).det ∈ S := by sorry
