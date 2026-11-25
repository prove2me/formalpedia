-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_eh_gl
-- name    : Formalism.FourierDecayAlt.P.Qx5.eh_gl
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:45:00.35715+00:00
-- url     : https://prove2.me/theorems/dc44b857-1a62-4f4d-9bc7-0d4fdc0f5a64
-- title:
--   Qx5: eh gl
-- statement:
--   The Qx5 construction uses the eh gl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1364-L1389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1364-L1389

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Qx2
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

theorem Formalism.FourierDecayAlt.P.Qx5.eh_gl {f : Mx k r → E} (hf : SmoothLev k r i D f) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (a b c d : Fin (mdim k r i)) :
    EH k r (posL k r i a) (posL k r i b) (EH k r (posL k r i c) (posL k r i d) f) g -
        EH k r (posL k r i c) (posL k r i d) (EH k r (posL k r i a) (posL k r i b) f) g =
      (if b = c then EH k r (posL k r i a) (posL k r i d) f g else 0) -
        (if d = a then EH k r (posL k r i c) (posL k r i b) f g else 0) := by sorry
