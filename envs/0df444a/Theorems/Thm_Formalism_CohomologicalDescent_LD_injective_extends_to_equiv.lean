-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_injective_extends_to_equiv
-- name    : Formalism.CohomologicalDescent.LD.injective_extends_to_equiv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:06:34.830534+00:00
-- url     : https://prove2.me/theorems/a6fb0ff5-2378-4c25-9330-e57fe91a9be1
-- title:
--   LD: injective extends to equiv
-- statement:
--   The LD construction uses the injective extends to equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L314-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L314-L324

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA

theorem Formalism.CohomologicalDescent.LD.injective_extends_to_equiv {r s t : ℕ} (h : s + t = r) (f : Fin s → Fin r) (hf : Function.Injective f) :
    ∃ ρ : Fin s ⊕ Fin t ≃ Fin r, ∀ p, ρ (Sum.inl p) = f p := by sorry
