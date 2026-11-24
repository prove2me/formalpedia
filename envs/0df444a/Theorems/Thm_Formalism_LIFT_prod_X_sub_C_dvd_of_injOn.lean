-- Prove2me | Theorems.Thm_Formalism_LIFT_prod_X_sub_C_dvd_of_injOn
-- name    : Formalism.LIFT.prod_X_sub_C_dvd_of_injOn
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T09:50:16.506159+00:00
-- url     : https://prove2.me/theorems/4b07a721-6b0c-481c-8a4b-341e42ea95bc
-- title:
--   LIFT: prod X sub C dvd of inj On
-- statement:
--   The LIFT construction uses the prod X sub C dvd of inj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/LagrangeIdeal.lean#L9-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/LagrangeIdeal.lean#L9-L26

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_LagrangeIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
open Polynomial

theorem Formalism.LIFT.prod_X_sub_C_dvd_of_injOn {R : Type} [CommRing R] [IsDomain R] {ι : Type}
    (S : Finset ι) (c : ι → R) (hc : Set.InjOn c S) (G : R[X])
    (hG : ∀ a ∈ S, G.eval (c a) = 0) : (∏ a ∈ S, (X - C (c a))) ∣ G := by sorry
