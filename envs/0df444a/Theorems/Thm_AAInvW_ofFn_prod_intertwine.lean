-- Prove2me | Theorems.Thm_AAInvW_ofFn_prod_intertwine
-- name    : AAInvW.ofFn_prod_intertwine
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:25:43.953202+00:00
-- url     : https://prove2.me/theorems/d393e110-01af-442c-8f6e-24cd75cd9f60
-- title:
--   AAInv W: of Fn prod intertwine
-- statement:
--   The AAInv W construction uses the of Fn prod intertwine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OfFnProdIntertwine.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OfFnProdIntertwine.lean#L13-L24

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OpModel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_DetTransposeApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OfFnProdIntertwine
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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem AAInvW.ofFn_prod_intertwine {A : Type*} [Ring A] (ρ : A) :
    ∀ (t : ℕ) (X Y : Fin t → A), (∀ k, X k * ρ = ρ * Y k) →
      (List.ofFn X).prod * ρ = ρ * (List.ofFn Y).prod := by sorry
