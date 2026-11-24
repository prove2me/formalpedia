-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_norm_hcompl
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z5.norm_hcompl
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:33:28.097861+00:00
-- url     : https://prove2.me/theorems/f22b6cca-75c5-4a09-8275-3f1598c32f0e
-- title:
--   Z5: norm hcompl
-- statement:
--   The Z5 construction uses the norm hcompl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZGlueA.lean#L355-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZGlueA.lean#L355-L386

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

theorem Formalism.L2.SG.Pf.LatDictZ.Z5.norm_hcompl (p : Ideal (𝓞 I.E)) [hp : p.IsPrime] (s : 𝓞 I.E)
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := I.E) p) :
    ∃ a : 𝓞 I.F, algebraMap (𝓞 I.F) (𝓞 I.E) a ∉ p ∧ ∃ t : 𝓞 I.E, algebraMap (𝓞 I.F) (𝓞 I.E) a = t * s := by sorry
