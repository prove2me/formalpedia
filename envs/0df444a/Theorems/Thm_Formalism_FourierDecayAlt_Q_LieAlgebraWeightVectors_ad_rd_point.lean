-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_rd_point
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_rd_point
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:45:18.909385+00:00
-- url     : https://prove2.me/theorems/94afd740-2cba-4a6f-b75e-0c187a870548
-- title:
--   Lie Algebra Weight Vectors: ad rd point
-- statement:
--   The Lie Algebra Weight Vectors construction uses the ad rd point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/AdUnitBLie.lean#L92-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/AdUnitBLie.lean#L92-L141

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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_rd_point {F : Mx k r → (Wq →L[ℂ] Wp)} (hF : F ∈ AdK k r z π D) {g : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r) ∩ D) (hgi : g⁻¹ * g = 1) (hgi' : g * g⁻¹ = 1) (hgU : IsUnit g)
    (hginv : g⁻¹ ∈ UH (Hpk k r)) {X : Mx k r} (hX : inLieLev k r (Fin.last r) X)
    (hXz : X *ᵥ (g⁻¹ *ᵥ z) = 0) (v : Wq) :
    RdV X F g v = dRep π (g * X * g⁻¹) (F g v) := by sorry
