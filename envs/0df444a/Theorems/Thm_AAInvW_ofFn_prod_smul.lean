-- Prove2me | Theorems.Thm_AAInvW_ofFn_prod_smul
-- name    : AAInvW.ofFn_prod_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:54:45.768125+00:00
-- url     : https://prove2.me/theorems/4b4b2453-c396-4627-b2d9-72e6c2cb508b
-- title:
--   AAInv W: of Fn prod smul
-- statement:
--   The AAInv W construction uses the of Fn prod smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OfFnProdSmul.lean#L29-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OfFnProdSmul.lean#L29-L41

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OfFnProdSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open AAInvW
open Formalism.REAL

theorem AAInvW.ofFn_prod_smul {A : Type*} [Ring A] [Algebra ℂ A] :
    ∀ (t : ℕ) (w : Fin t → ℂ) (X : Fin t → A),
      (List.ofFn fun k => w k • X k).prod = (∏ k, w k) • (List.ofFn X).prod := by sorry
