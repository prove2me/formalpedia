-- Prove2me | Theorems.Thm_AAInvW_ana_hpart_unique
-- name    : AAInvW.ana_hpart_unique
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:55:57.581463+00:00
-- url     : https://prove2.me/theorems/59eff1a3-361a-4a37-9fc3-610ab71aa6a8
-- title:
--   AAInv W: ana hpart unique
-- statement:
--   The AAInv W construction uses the ana hpart unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/AnaHpartUnique.lean#L123-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/AnaHpartUnique.lean#L123-L133

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

theorem AAInvW.ana_hpart_unique (hH : HInvol H) {P Q : Matrix (Fin n) (Fin n) ℂ} (hP : inLH H P) (hQ : inLH H Q) :
    hpart1 H (P + Complex.I • Q) = P ∧ hpart2 H (P + Complex.I • Q) = Q := by sorry
