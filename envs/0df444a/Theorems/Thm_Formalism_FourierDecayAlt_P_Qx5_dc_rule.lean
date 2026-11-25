-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_dc_rule
-- name    : Formalism.FourierDecayAlt.P.Qx5.dc_rule
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:44:28.074442+00:00
-- url     : https://prove2.me/theorems/cb2c77e3-8385-4eca-9243-09445f2a7af9
-- title:
--   Qx5: dc rule
-- statement:
--   The Qx5 construction uses the dc rule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L2008-L2056
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L2008-L2056

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

theorem Formalism.FourierDecayAlt.P.Qx5.dc_rule (h : ComRule k r i D E c g ρ κ s d) (hc : SmoothLev k r i D c) {t : ℕ}
    (a b : Fin t → Fin (mdim k r i)) (w : ℂ) {f : Mx k r → E} (hf : SmoothLev k r i D f) :
    Mop k r i a b w (fun y => c y • c y • f y) g =
      (2 * c g) • Mop k r i a b w (fun y => c y • f y) g - (c g ^ 2) • Mop k r i a b w f g := by sorry
