-- Prove2me | Theorems.Thm_AAInvW_tm_conj
-- name    : AAInvW.tm_conj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:55:25.329804+00:00
-- url     : https://prove2.me/theorems/356b48d4-5db6-4cda-a19c-9194373bfd7f
-- title:
--   AAInv W: tm conj
-- statement:
--   The AAInv W construction uses the tm conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OfFnProdSmul.lean#L43-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OfFnProdSmul.lean#L43-L58

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

theorem AAInvW.tm_conj {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (x : ℂ) (i j : Fin n) :
    Tm (fun i j => ∑ c, ∑ d, (P c i * Q j d) • E c d) x i j =
      ∑ p : Fin n × Fin n, (P p.1 i * Q j p.2) • Tm E x p.1 p.2 := by sorry
