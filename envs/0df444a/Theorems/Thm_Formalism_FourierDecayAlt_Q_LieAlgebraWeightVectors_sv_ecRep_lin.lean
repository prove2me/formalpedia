-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_ecRep_lin
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_ecRep_lin
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:45:47.212106+00:00
-- url     : https://prove2.me/theorems/f4b5dd6b-c6d4-4bce-8643-0b3411063b25
-- title:
--   Lie Algebra Weight Vectors: sv ec Rep lin
-- statement:
--   The Lie Algebra Weight Vectors construction uses the sv ec Rep lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/SmoothVec.lean#L190-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/SmoothVec.lean#L190-L202

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SmoothVec
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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
  {π : Mx k r → (Wp →L[ℂ] Wp)}

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_ecRep_lin (hall : ∀ v : Wp, v ∈ SmVec k r z π) {Z : Mx k r}
    (h1 : inLieW k r z (hpart1 (Hpk k r) Z)) (h2 : inLieW k r z (hpart2 (Hpk k r) Z)) :
    IsLinearMap ℂ (EcRep (Hpk k r) π Z) := by sorry
