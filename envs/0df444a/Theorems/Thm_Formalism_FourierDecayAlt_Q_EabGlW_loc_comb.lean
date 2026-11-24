-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_loc_comb
-- name    : Formalism.FourierDecayAlt.Q.EabGlW.loc_comb
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:41:20.303655+00:00
-- url     : https://prove2.me/theorems/0fe46c41-4c60-4435-b4bb-0adbd14482aa
-- title:
--   Eab Gl W: loc comb
-- statement:
--   The Eab Gl W construction uses the loc comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/ExpMulVecFix.lean#L91-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/ExpMulVecFix.lean#L91-L115

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabGlW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.Q.EabGlW.loc_comb {G : Set (Matrix (Fin n) (Fin n) ℂ)} {V A B : Matrix (Fin n) (Fin n) ℂ}
    (hV : Flow G V) (hA : Flow G A) (hB : Flow G B)
    {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hL : LocExt G f F U)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ U) (hgG : g ∈ G) (c : ℂ) :
    RdV V (fun h => RdV A f h + c • RdV B f h) g = RdV V (RdV A f) g + c • RdV V (RdV B f) g := by sorry
