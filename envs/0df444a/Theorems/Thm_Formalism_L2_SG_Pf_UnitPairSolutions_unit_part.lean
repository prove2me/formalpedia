-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_UnitPairSolutions_unit_part
-- name    : Formalism.L2.SG.Pf.UnitPairSolutions.unit_part
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:59:07.752027+00:00
-- url     : https://prove2.me/theorems/d3b082f1-7efa-5dc6-afea-48fe8b53f2e8
-- title:
--   Unit Pair Solutions: unit part
-- statement:
--   The Unit Pair Solutions construction uses the unit part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/SmulMemLocFOfSP.lean#L50-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/SmulMemLocFOfSP.lean#L50-L80

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

theorem Formalism.L2.SG.Pf.UnitPairSolutions.unit_part (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {π s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π s₀) {a : 𝓞 F} (ha : a ≠ 0) :
    (algebraMap F K (a : F))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 a ∈ SP K 𝔭 := by sorry
