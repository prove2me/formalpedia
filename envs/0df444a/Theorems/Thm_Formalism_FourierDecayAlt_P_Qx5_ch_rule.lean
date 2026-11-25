-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_ch_rule
-- name    : Formalism.FourierDecayAlt.P.Qx5.ch_rule
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:54:13.262776+00:00
-- url     : https://prove2.me/theorems/1fd6308d-dbfc-4b8b-8888-30c603cf29e0
-- title:
--   Qx5: ch rule
-- statement:
--   The Qx5 construction uses the ch rule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1992-L2006
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1992-L2006

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

theorem Formalism.FourierDecayAlt.P.Qx5.ch_rule (h : ComRule k r i D E c g ρ κ s d) (A B : Fin (mdim k r i) → ℂ) (w : ℂ) {f : Mx k r → E}
    (hf : SmoothLev k r i D f) :
    ch k r i A B w (fun y => c y • f y) g = c g • ch k r i A B w f g + s • ch2 k r i A ρ B κ (w - d) f g := by sorry
