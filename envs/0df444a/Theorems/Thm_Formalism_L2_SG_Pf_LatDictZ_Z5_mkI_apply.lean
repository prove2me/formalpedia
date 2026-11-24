-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_mkI_apply
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z5.mkI_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:29:42.538803+00:00
-- url     : https://prove2.me/theorems/c4577ad8-f499-447d-ae17-71b8f8d0f68d
-- title:
--   Z5: mk I apply
-- statement:
--   The Z5 construction uses the mk I apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZGlueA.lean#L98-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZGlueA.lean#L98-L99

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZGlueA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z5
open Formalism.MainNotions.S PIW.AdelClassFin Formalism.L2.SG.Pf.LatDictZ
variable {F : Type} [Field F] [NumberField F]

theorem Formalism.L2.SG.Pf.LatDictZ.Z5.mkI_apply (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hc : ∀ v, c v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) : mkI c hc v = c v := by sorry
