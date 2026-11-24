-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_geom_package
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.geom_package
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:20:11.526025+00:00
-- url     : https://prove2.me/theorems/470b71ec-66f7-43fa-8b27-bcbc6cd84cd8
-- title:
--   Lie Algebra Weight Vectors: geom package
-- statement:
--   The Lie Algebra Weight Vectors construction uses the geom package property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/ExistsFrameOfPositiveVector.lean#L312-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/ExistsFrameOfPositiveVector.lean#L312-L359

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_ExistsFrameOfPositiveVector
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
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.geom_package {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z)
    (hT' : 0 < Tz k r z') {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hGG : GGl k r z z' g ≠ 0) :
    ∃ (Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ) (e' e : Fin (2 * r + k + 1) → ℂ),
      IsFrameOf k r [g⁻¹ *ᵥ z, z'] Bs ∧
      inWb k r e' ∧ herm (Hpk k r) e' z' = 0 ∧ herm (Hpk k r) e' e' = 1 ∧ IsFrameOf k r [z', e'] Bs ∧
      inWb k r e ∧ herm (Hpk k r) e z = 0 ∧ herm (Hpk k r) e e = 1 ∧
      IsFrameOf k r [z, e] (fun a => g *ᵥ Bs a) := by sorry
