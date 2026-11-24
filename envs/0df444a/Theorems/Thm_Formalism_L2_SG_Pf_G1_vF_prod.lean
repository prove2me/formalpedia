-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G1_vF_prod
-- name    : Formalism.L2.SG.Pf.G1.vF_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:17.339309+00:00
-- url     : https://prove2.me/theorems/104808d7-4a92-4053-a563-3e435012d683
-- title:
--   G1: v F prod
-- statement:
--   The G1 construction uses the v F prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/AlmostEverywhereSpherical.lean#L54-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/AlmostEverywhereSpherical.lean#L54-L62

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsOrthGen
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AlmostEverywhereSpherical
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G1
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {F : Type} [Field F] [NumberField F] {𝔭 : Ideal (𝓞 F)}

theorem Formalism.L2.SG.Pf.G1.vF_prod (h𝔭 : 𝔭.IsMaximal) {ι : Type*} (s : Finset ι) (f : ι → 𝓞 F) (hf : ∀ i, f i ≠ 0) :
    vF 𝔭 (∏ i ∈ s, f i) = ∑ i ∈ s, vF 𝔭 (f i) := by sorry
