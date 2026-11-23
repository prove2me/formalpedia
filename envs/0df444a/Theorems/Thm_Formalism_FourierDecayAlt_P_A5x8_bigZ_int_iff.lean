-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_bigZ_int_iff
-- name    : Formalism.FourierDecayAlt.P.A5x8.bigZ_int_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:00.530152+00:00
-- url     : https://prove2.me/theorems/8af04443-c57a-4169-8041-b89879ae9d70
-- title:
--   A5x8: big Z int iff
-- statement:
--   The A5x8 construction uses the big Z int iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L1583-L1616
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L1583-L1616

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] (R : Subring K) {m : ℕ}

theorem Formalism.FourierDecayAlt.P.A5x8.bigZ_int_iff {N : ℕ} (hN : N = m + 1) (Z : Matrix (Fin m) (Fin m) K) (hZ : IsInt R Z)
    (hd : IsUnit Z.det) (α : coker R Z →ₗ[R] KR R) (β : coker R Z) (c : K) :
    IsInt R (bigZ hN Z (outV R (iA R Z α)) (outV R (iC R Z β)) c) ↔
      α β = -(Submodule.Quotient.mk c : KR R) := by sorry
