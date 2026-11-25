-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_weyl_le_of_stable_submodule
-- name    : Formalism.CohomologicalDescent.LD.weyl_le_of_stable_submodule
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:07:41.766015+00:00
-- url     : https://prove2.me/theorems/0985c352-0848-436b-ae6d-8111527a8db6
-- title:
--   LD: weyl le of stable submodule
-- statement:
--   The LD construction uses the weyl le of stable submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L729-L774
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L729-L774

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

theorem Formalism.CohomologicalDescent.LD.weyl_le_of_stable_submodule {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) (L : Submodule ℤ (MvPolynomial (Fin r × Fin r) ℤ))
    (h0 : hw ℤ le_rfl ν ∈ L)
    (hs : ∀ a b : Fin r, a ≠ b → ∀ (k : ℕ) (f : MvPolynomial (Fin r × Fin r) ℤ), f ∈ L → rowDiv ℤ a b k f ∈ L) :
    weyl ℤ r r le_rfl ν ≤ L := by sorry
