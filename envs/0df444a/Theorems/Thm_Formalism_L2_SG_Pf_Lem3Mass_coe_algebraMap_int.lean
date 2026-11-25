-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Lem3Mass_coe_algebraMap_int
-- name    : Formalism.L2.SG.Pf.Lem3Mass.coe_algebraMap_int
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:40:40.122738+00:00
-- url     : https://prove2.me/theorems/72d64cf8-128c-5dab-8b56-991152663898
-- title:
--   Lem3 Mass: coe algebra Map int
-- statement:
--   The Lem3 Mass construction uses the coe algebra Map int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsDenOfLeOne.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsDenOfLeOne.lean#L47-L49

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IsUnitDetOfIsometry
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsSubDivMemSP
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsDenOfLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Lem3Mass
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.UnitaryGroupLocal
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology Filter
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F))
variable (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hfix : ∀ y : E, σ y = y → y ∈ (algebraMap F E).range)

theorem Formalism.L2.SG.Pf.Lem3Mass.coe_algebraMap_int (t : 𝓞 F) :
    algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t) = algebraMap F E (t : F) := by sorry
