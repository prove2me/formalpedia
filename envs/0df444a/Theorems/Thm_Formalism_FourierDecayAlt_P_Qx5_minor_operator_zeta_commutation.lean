-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_minor_operator_zeta_commutation
-- name    : Formalism.FourierDecayAlt.P.Qx5.minor_operator_zeta_commutation
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:47:35.515934+00:00
-- url     : https://prove2.me/theorems/30949381-030b-48d9-8a92-6de149c5b25f
-- title:
--   Qx5: minor operator zeta commutation
-- statement:
--   The Qx5 construction uses the minor operator zeta commutation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1790-L1803
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1790-L1803

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
variable (z z' : Fin (2 * r + k + 1) → ℂ)

theorem Formalism.FourierDecayAlt.P.Qx5.minor_operator_zeta_commutation (hD : IsOpen D) {t : ℕ} (a b : Fin (t + 1) → Fin (mdim k r i)) (w : ℂ) {f : Mx k r → E}
    (hf : SmoothLev k r i D f) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    Mop k r i a b w (fun y => zbF k r z z' i y • f y) g = zbF k r z z' i g • Mop k r i a b w f g -
      ∑ p : Fin (t + 1), ∑ q : Fin (t + 1), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * xbv k r z' i (a p) * yv k r z i g (b q)) •
        Mop k r i (a ∘ p.succAbove) (b ∘ q.succAbove) w f g := by sorry
