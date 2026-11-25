-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_UnitPairSolutions_smul_mem_locF_of_SP
-- name    : Formalism.L2.SG.Pf.UnitPairSolutions.smul_mem_locF_of_SP
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:48:43.075803+00:00
-- url     : https://prove2.me/theorems/17a541e0-a0e3-5496-b889-caece26dd92a
-- title:
--   Unit Pair Solutions: smul mem loc F of SP
-- statement:
--   The Unit Pair Solutions construction uses the smul mem loc F of SP property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/SmulMemLocFOfSP.lean#L189-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/SmulMemLocFOfSP.lean#L189-L196

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_InPOfMemPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SmulMemLocFOfSP
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.UnitPairSolutions
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.GluingBases
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.L2.SG.Pf.UnitPairSolutions.smul_mem_locF_of_SP {𝔭 : Ideal (𝓞 F)} [hp : 𝔭.IsPrime] {L : Submodule (𝓞 K) V} {r : K}
    (hr : r ∈ SP K 𝔭) {v : V} (hv : v ∈ L) : r • v ∈ locF 𝔭 L := by sorry
