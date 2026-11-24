-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_glue
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z5.glue
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:54:23.620116+00:00
-- url     : https://prove2.me/theorems/f39d2b03-f5f8-42a0-a503-f0c074d5da63
-- title:
--   Z5: glue
-- statement:
--   The Z5 construction uses the glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZGlueA.lean#L295-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZGlueA.lean#L295-L353

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

theorem Formalism.L2.SG.Pf.LatDictZ.Z5.glue (T : Set (HeightOneSpectrum (𝓞 I.F))) (w : Fin I.n → I.E)
    (h : ∀ q ∈ T, ∃ a : 𝓞 I.F, a ∉ q.asIdeal ∧ algebraMap (𝓞 I.F) (𝓞 I.E) a • w ∈ I.L) :
    iA I (eT T) • iv I w ∈ I.Lf := by sorry
