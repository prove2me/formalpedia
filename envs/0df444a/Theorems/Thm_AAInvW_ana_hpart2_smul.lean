-- Prove2me | Theorems.Thm_AAInvW_ana_hpart2_smul
-- name    : AAInvW.ana_hpart2_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:56:21.876101+00:00
-- url     : https://prove2.me/theorems/5928e060-0e60-4b3f-80f3-f889bef9578f
-- title:
--   AAInv W: ana hpart2 smul
-- statement:
--   The AAInv W construction uses the ana hpart2 smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/AnaHpartUnique.lean#L167-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/AnaHpartUnique.lean#L167-L174

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
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
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}

theorem AAInvW.ana_hpart2_smul (hH : HInvol H) (x y : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    hpart2 H (((x : ℂ) + (y : ℂ) * Complex.I) • Z) = (x : ℂ) • hpart2 H Z + (y : ℂ) • hpart1 H Z := by sorry
