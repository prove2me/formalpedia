-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_capelli_two_commutation_rule
-- name    : Formalism.FourierDecayAlt.P.Qx5.capelli_two_commutation_rule
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:46:22.989801+00:00
-- url     : https://prove2.me/theorems/7ea76818-047a-4d6b-8e19-e76815062efc
-- title:
--   Qx5: capelli two commutation rule
-- statement:
--   The Qx5 construction uses the capelli two commutation rule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L2070-L2085
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L2070-L2085

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
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
variable {c : Mx k r → ℂ} {g : Mx k r} {ρ κ : Fin (mdim k r i) → ℂ} {s d : ℂ}

theorem Formalism.FourierDecayAlt.P.Qx5.capelli_two_commutation_rule (h : ComRule k r i D E c g ρ κ s d) (hs : s ≠ 0) (hc : SmoothLev k r i D c)
    (A B : Fin (mdim k r i) → ℂ) (w : ℂ) {f : Mx k r → E} (hf : SmoothLev k r i D f) :
    ch2 k r i A ρ B κ (w - d) (fun y => c y • f y) g = c g • ch2 k r i A ρ B κ (w - d) f g := by sorry
