-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_UnitPairSolutions_pair_coeffs_mem
-- name    : Formalism.L2.SG.Pf.UnitPairSolutions.pair_coeffs_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:51:12.175053+00:00
-- url     : https://prove2.me/theorems/c06e905a-c664-570c-b061-71093825f4c3
-- title:
--   Unit Pair Solutions: pair coeffs mem
-- statement:
--   The Unit Pair Solutions construction uses the pair coeffs mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/SmulMemLocFOfSP.lean#L176-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/SmulMemLocFOfSP.lean#L176-L183

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

theorem Formalism.L2.SG.Pf.UnitPairSolutions.pair_coeffs_mem {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {q a c r X Y : K}
    (hp : q ∈ SP K 𝔭) (hua : a⁻¹ * q ∈ SP K 𝔭) (huc : c⁻¹ * q ∈ SP K 𝔭) (hr : r ∈ SP K 𝔭)
    (hX : X ∈ SP K 𝔭) (hY : Y ∈ SP K 𝔭) :
    X * q * (a⁻¹ * q) - Y * (a⁻¹ * q) ∈ SP K 𝔭 ∧
      Y * r * (a⁻¹ * q) * (c⁻¹ * q) - X * (a⁻¹ * q) ∈ SP K 𝔭 := by sorry
