-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_ev_EM
-- name    : Formalism.FourierDecayAlt.P.Qx5.ev_EM
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:59:40.498313+00:00
-- url     : https://prove2.me/theorems/be607844-f185-48e0-b533-98b06052e807
-- title:
--   Qx5: ev EM
-- statement:
--   The Qx5 construction uses the ev EM property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1560-L1566
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1560-L1566

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

theorem Formalism.FourierDecayAlt.P.Qx5.ev_EM (hD : IsOpen D) (a b : Fin (mdim k r i)) {c : Mx k r → ℂ} (hc : SmoothLev k r i D c) (v : VS k r i D E)
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    (Eh hD a b (Mh hD c hc v) : Mx k r → E) g =
      c g • EH k r (posL k r i a) (posL k r i b) (v : Mx k r → E) g +
        EH k r (posL k r i a) (posL k r i b) c g • (v : Mx k r → E) g := by sorry
