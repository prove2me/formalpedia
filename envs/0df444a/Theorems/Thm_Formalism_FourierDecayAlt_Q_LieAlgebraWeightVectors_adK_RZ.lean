-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_adK_RZ
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.adK_RZ
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:46:44.571494+00:00
-- url     : https://prove2.me/theorems/91025d91-123a-4a54-81a2-b0d6268fd932
-- title:
--   Lie Algebra Weight Vectors: ad K RZ
-- statement:
--   The Lie Algebra Weight Vectors construction uses the ad K RZ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/AdUnitBLie.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/AdUnitBLie.lean#L78-L81

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBCtMulVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBLie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx2
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.adK_RZ (hD : IsOpen D) {Z : Mx k r} (h1 : inLieLev k r (Fin.last r) (hpart1 (Hpk k r) Z))
    (h2 : inLieLev k r (Fin.last r) (hpart2 (Hpk k r) Z)) {F : Mx k r → (Wq →L[ℂ] Wp)}
    (hF : F ∈ AdK k r z π D) : RZ (Hpk k r) Z F ∈ AdK k r z π D := by sorry
