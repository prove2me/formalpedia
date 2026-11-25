-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_hasDerivAt_polyDb
-- name    : Formalism.FourierDecayAlt.P.MinorPolynomials.hasDerivAt_polyDb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:33:38.647719+00:00
-- url     : https://prove2.me/theorems/0b4c1679-4090-4d8b-98c9-ccd3fd6bcecb
-- title:
--   Minor Polynomials: has Deriv At poly Db
-- statement:
--   The Minor Polynomials construction uses the has Deriv At poly Db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtInvpow.lean#L194-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtInvpow.lean#L194-L198

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsVecApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetClassEstimate
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_DegPderivMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Expand
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtInvpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.MinorPolynomials.hasDerivAt_polyDb (X g : Mat k r) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    HasDerivAt (fun t => star (Dmin k r z z' (crv (false, X) g t) l)) (eval (vars g) (dP X (qDbl z z' l))) 0 := by sorry
