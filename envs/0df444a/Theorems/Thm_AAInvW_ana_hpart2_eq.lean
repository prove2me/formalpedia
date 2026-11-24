-- Prove2me | Theorems.Thm_AAInvW_ana_hpart2_eq
-- name    : AAInvW.ana_hpart2_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:31:19.68232+00:00
-- url     : https://prove2.me/theorems/5709f2e8-a52f-4349-b4b2-b8c2cf5604cc
-- title:
--   AAInv W: ana hpart2 eq
-- statement:
--   The AAInv W construction uses the ana hpart2 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/AnaHpartUnique.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/AnaHpartUnique.lean#L92-L94

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

theorem AAInvW.ana_hpart2_eq (hH : HInvol H) (Z : Matrix (Fin n) (Fin n) ℂ) :
    hpart2 H Z = (1 / (2 * Complex.I) : ℂ) • (Z + H * Zᴴ * H) := by sorry
