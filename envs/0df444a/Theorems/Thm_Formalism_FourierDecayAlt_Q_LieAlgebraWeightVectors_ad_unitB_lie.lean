-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_unitB_lie
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_unitB_lie
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:07:24.412203+00:00
-- url     : https://prove2.me/theorems/6fae2fe7-0f62-4e3b-996d-5f101a33870f
-- title:
--   Lie Algebra Weight Vectors: ad unit B lie
-- statement:
--   The Lie Algebra Weight Vectors construction uses the ad unit B lie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/AdUnitBLie.lean#L160-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/AdUnitBLie.lean#L160-L180

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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_unitB_lie {g : Mx k r} {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hBs : IsFrameOf k r [g⁻¹ *ᵥ z] Bs) (a b : Fin m) :
    (inLieLev k r (Fin.last r) (hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b)) ∧
      inLieLev k r (Fin.last r) (hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b))) ∧
    (hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b) *ᵥ (g⁻¹ *ᵥ z) = 0 ∧
      hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b) *ᵥ (g⁻¹ *ᵥ z) = 0) := by sorry
