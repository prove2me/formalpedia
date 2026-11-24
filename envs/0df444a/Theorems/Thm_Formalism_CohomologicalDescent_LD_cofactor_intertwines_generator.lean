-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_intertwines_generator
-- name    : Formalism.CohomologicalDescent.LD.cofactor_intertwines_generator
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:14:04.04662+00:00
-- url     : https://prove2.me/theorems/09adc898-3c6c-48ac-b602-23e1dd156164
-- title:
--   LD: cofactor intertwines generator
-- statement:
--   The LD construction uses the cofactor intertwines generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L809-L831
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L809-L831

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

theorem Formalism.CohomologicalDescent.LD.cofactor_intertwines_generator {r : ℕ} (a b : Fin r) (hab : a ≠ b) (x : MvPolynomial (Fin r × Fin r) ℤ) :
    rowGen ℤ a b (cofMap r x) =
      Polynomial.eval₂ (Polynomial.C.comp (cofMap r).toRingHom) (-Polynomial.X)
        (rowGen ℤ (Fin.rev b) (Fin.rev a) x) := by sorry
