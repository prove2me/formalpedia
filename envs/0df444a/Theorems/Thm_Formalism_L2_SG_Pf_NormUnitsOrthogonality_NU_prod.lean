-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_NormUnitsOrthogonality_NU_prod
-- name    : Formalism.L2.SG.Pf.NormUnitsOrthogonality.NU.prod
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:07:04.201502+00:00
-- url     : https://prove2.me/theorems/3e5ce2a0-7e51-5c53-bc4b-a253c2558905
-- title:
--   NU: prod
-- statement:
--   The NU construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/LinIndOrth.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/LinIndOrth.lean#L66-L69

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DualFormInverse
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LinIndOrth
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NormUnitsOrthogonality
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime]

theorem Formalism.L2.SG.Pf.NormUnitsOrthogonality.NU.prod {ι : Type} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, NU 𝔭 (f i)) :
    NU 𝔭 (∏ i ∈ s, f i) := by sorry
