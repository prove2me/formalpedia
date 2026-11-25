-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G6_gmap_orthK
-- name    : Formalism.L2.SG.Pf.G6.gmap_orthK
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:30:05.028807+00:00
-- url     : https://prove2.me/theorems/c752952e-37e4-5f49-8b24-5f9f91668032
-- title:
--   G6: gmap orth K
-- statement:
--   The G6 construction uses the gmap orth K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/GmapEqSelfOfFix.lean#L60-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/GmapEqSelfOfFix.lean#L60-L71

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SameGenusFix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_GmapEqSelfOfFix
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G6
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.L2.SG.Pf.G6.gmap_orthK {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) :
    Formalism.HermitianLatticesTheory.gmap g ((orthK h U).restrictScalars (𝓞 K)) = (orthK h U).restrictScalars (𝓞 K) := by sorry
