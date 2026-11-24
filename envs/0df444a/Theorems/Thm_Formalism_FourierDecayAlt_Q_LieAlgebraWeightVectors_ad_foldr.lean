-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_foldr
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_foldr
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:45:30.197801+00:00
-- url     : https://prove2.me/theorems/032007e9-8cb6-4306-aae2-600a61b69e10
-- title:
--   Lie Algebra Weight Vectors: ad foldr
-- statement:
--   The Lie Algebra Weight Vectors construction uses the ad foldr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/AdUnitBLie.lean#L200-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/AdUnitBLie.lean#L200-L210

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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_foldr {ι X Y : Type*} (K : Set X) (P : X → Y) (l : List ι) (T : ι → X → X) (T' : ι → Y → Y)
    (hK : ∀ j, ∀ x ∈ K, T j x ∈ K) (hP : ∀ j, ∀ x ∈ K, P (T j x) = T' j (P x)) (x : X) (hx : x ∈ K) :
    (l.map T).foldr (fun S h => S h) x ∈ K ∧
      P ((l.map T).foldr (fun S h => S h) x) = (l.map T').foldr (fun S h => S h) (P x) := by sorry
