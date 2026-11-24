-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ff_smul
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ff_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:44:11.750097+00:00
-- url     : https://prove2.me/theorems/2f8a6d15-1043-497f-907a-cd35a04bb2f7
-- title:
--   Lie Algebra Weight Vectors: ff smul
-- statement:
--   The Lie Algebra Weight Vectors construction uses the ff smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/TopLevelPointwiseIdentity.lean#L168-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/TopLevelPointwiseIdentity.lean#L168-L181

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_TopLevelPointwiseIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ff_smul {J : Mx k r → (Wq →L[ℂ] Wp)} (h : J ∈ FFl k r z z' π π' (Fin.last r) D) (c : ℂ) :
    (fun x => c • J x) ∈ FFl k r z z' π π' (Fin.last r) D := by sorry
