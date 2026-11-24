-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G1_isSymm_smul
-- name    : Formalism.L2.SG.Pf.G1.isSymm_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:43.111098+00:00
-- url     : https://prove2.me/theorems/2b33e19d-9602-4ca2-aa6f-5f77d4be1866
-- title:
--   G1: is Symm smul
-- statement:
--   The G1 construction uses the is Symm smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsOrthGen.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsOrthGen.lean#L25-L28

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

theorem Formalism.L2.SG.Pf.G1.isSymm_smul {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {c : K} (hc : star c = c) :
    (c • h).IsSymm := by sorry
