-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_GluingBases_inP_of_mem_pow
-- name    : Formalism.L2.SG.Pf.GluingBases.inP_of_mem_pow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:46:08.067623+00:00
-- url     : https://prove2.me/theorems/194bbfe9-0801-5711-84d5-85f68ebb085d
-- title:
--   Gluing Bases: in P of mem pow
-- statement:
--   The Gluing Bases construction uses the in P of mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/InPOfMemPow.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/InPOfMemPow.lean#L22-L27

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_GlueLocalOfFam
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AlmostEverywhereSpherical
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeOfFibLocNeZeroGood
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_InPOfMemPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.GluingBases
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.L2.SG.Pf.GluingBases.inP_of_mem_pow {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k : ℕ} {t : 𝓞 F} (ht : t ∈ 𝔭 ^ k) :
    InP 𝔭 k (algebraMap F K (t : F)) := by sorry
