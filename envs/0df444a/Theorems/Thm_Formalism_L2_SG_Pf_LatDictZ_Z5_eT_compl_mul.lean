-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_eT_compl_mul
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z5.eT_compl_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:35:59.764556+00:00
-- url     : https://prove2.me/theorems/1a82ecb2-2711-4ac9-8e1e-c4151865d8fa
-- title:
--   Z5: e T compl mul
-- statement:
--   The Z5 construction uses the e T compl mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZGlueA.lean#L156-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZGlueA.lean#L156-L167

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

theorem Formalism.L2.SG.Pf.LatDictZ.Z5.eT_compl_mul {Q : Set (HeightOneSpectrum (𝓞 F))} {i : HeightOneSpectrum (𝓞 F)} (hi : i ∈ Q) :
    eT Qᶜ * eT {i} = 0 := by sorry
