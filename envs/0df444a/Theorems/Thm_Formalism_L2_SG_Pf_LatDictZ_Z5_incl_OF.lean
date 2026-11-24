-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_incl_OF
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z5.incl_OF
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:34:38.534713+00:00
-- url     : https://prove2.me/theorems/5af47e56-b7fd-408c-9212-724d046e3ee9
-- title:
--   Z5: incl OF
-- statement:
--   The Z5 construction uses the incl OF property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZGlueA.lean#L237-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZGlueA.lean#L237-L245

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
variable (I : AutInst)

theorem Formalism.L2.SG.Pf.LatDictZ.Z5.incl_OF (a : 𝓞 I.F) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E (algebraMap (𝓞 I.F) (𝓞 I.E) a)) =
      iA I (algebraMap (𝓞 I.F) (Af I.F) a) := by sorry
