-- Prove2me | Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_NilradicalHermitianFrames_PF_eval
-- name    : Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.PF_eval
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:25.875122+00:00
-- url     : https://prove2.me/theorems/f08d4151-268c-403f-b7ce-00a10fda6c19
-- title:
--   Nilradical Hermitian Frames: PF eval
-- statement:
--   The Nilradical Hermitian Frames construction uses the PF eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/VolumeZeroFintype.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/VolumeZeroFintype.lean#L13-L19

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

theorem Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.PF_eval {ι : Type*} (p : MvPolynomial ι ℂ) (y : ι → ℝ) :
    (MvPolynomial.aeval (R := ℂ) (fun i (y : ι → ℝ) => (y i : ℂ)) p : (ι → ℝ) → ℂ) y =
      MvPolynomial.eval (fun i => (y i : ℂ)) p := by sorry
