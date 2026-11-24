-- Prove2me | Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_NilradicalHermitianFrames_PF_mem_iff
-- name    : Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.PF_mem_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:59.089855+00:00
-- url     : https://prove2.me/theorems/3b178c93-b089-46f1-9d98-e26bf4ddb1d3
-- title:
--   Nilradical Hermitian Frames: PF mem iff
-- statement:
--   The Nilradical Hermitian Frames construction uses the PF mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/VolumeZeroFintype.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/VolumeZeroFintype.lean#L21-L27

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

theorem Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.PF_mem_iff {ι : Type*} {f : (ι → ℝ) → ℂ} :
    f ∈ PF ι ↔ ∃ p : MvPolynomial ι ℂ, ∀ y, f y = MvPolynomial.eval (fun i => (y i : ℂ)) p := by sorry
