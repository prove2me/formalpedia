-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_comb_match
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.comb_match
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:45:11.696274+00:00
-- url     : https://prove2.me/theorems/6928b96a-4331-4184-88a2-eff668409bcf
-- title:
--   Lie Algebra Weight Vectors: comb match
-- statement:
--   The Lie Algebra Weight Vectors construction uses the comb match property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/CbStrictMonoOfAnti.lean#L219-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/CbStrictMonoOfAnti.lean#L219-L264

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti
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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.comb_match {P : M.Par} (hP : P.OK) :
    ∃ f : M.Ty P → M.Ty (Pp P), Function.Injective f ∧ (∀ (ρ : M.Ty P) (Y : ℂ), M.xC (Pp P) (f ρ) Y = M.xC P ρ Y) ∧
      ∀ (σ : M.Ty (Pp P)) (ρ : M.Ty (Pq P)), (∀ Y : ℂ, M.xC (Pp P) σ Y = M.xC (Pq P) ρ Y) → σ ∈ Set.range f := by sorry
