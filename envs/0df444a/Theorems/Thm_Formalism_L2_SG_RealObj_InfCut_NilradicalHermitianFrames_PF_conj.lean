-- Prove2me | Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_NilradicalHermitianFrames_PF_conj
-- name    : Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.PF_conj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T09:47:01.121176+00:00
-- url     : https://prove2.me/theorems/00d36213-5e25-4311-a296-bc763f8ceb62
-- title:
--   Nilradical Hermitian Frames: PF conj
-- statement:
--   The Nilradical Hermitian Frames construction uses the PF conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/VolumeZeroFintype.lean#L32-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/VolumeZeroFintype.lean#L32-L40

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_VolumeZeroFintype
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

theorem Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.PF_conj {ι : Type*} {f : (ι → ℝ) → ℂ} (hf : f ∈ PF ι) : (fun y => conj (f y)) ∈ PF ι := by sorry
