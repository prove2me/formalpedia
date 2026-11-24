-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_cT_gl
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z5.cT_gl
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:32:04.877545+00:00
-- url     : https://prove2.me/theorems/5dc51719-64f4-492e-947d-b4341e842f44
-- title:
--   Z5: c T gl
-- statement:
--   The Z5 construction uses the c T gl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZGlueA.lean#L78-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZGlueA.lean#L78-L86

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
variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.L2.SG.Pf.LatDictZ.Z5.cT_gl (σ : R →+* R) {s : Finset ι} {e : ι → R} (hσ : ∀ i ∈ s, σ (e i) = e i) (M : Matrix n n R)
    (A : ι → Matrix n n R) :
    Formalism.UG.cT σ (gl s e M A) = gl s e (Formalism.UG.cT σ M) (fun i => Formalism.UG.cT σ (A i)) := by sorry
