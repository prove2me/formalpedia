-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_reflection_carried_facts
-- name    : Formalism.CohomologicalDescent.WorkedExample.reflection_carried_facts
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:02:05.856845+00:00
-- url     : https://prove2.me/theorems/9a4b4038-f083-4d48-8ded-c04ea632f1b4
-- title:
--   Worked Example: reflection carried facts
-- statement:
--   The Worked Example construction uses the reflection carried facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L152-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L152-L168

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.WorkedExample
open Formalism.CohomologicalDescent

theorem Formalism.CohomologicalDescent.WorkedExample.reflection_carried_facts {ι : Type} {N : ℕ} (D : Labels ι N) (σ : Equiv.Perm ι) (h t : ℕ) (ep : ι → ι)
    (J : ι → Fin N → ℤ) (botJ : ι → ℤ) (hR : D.Refl σ h t) (hC : D.Carried ep J botJ) :
    (∀ i, ep (ep i) = i) ∧ (∀ i, σ (ep i) = ep (σ i)) ∧ (∀ i, J i = D.U' (ep i)) ∧
      (∀ i, botJ i = D.bot (ep i)) := by sorry
