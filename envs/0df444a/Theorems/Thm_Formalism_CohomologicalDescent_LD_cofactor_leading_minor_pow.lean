-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_leading_minor_pow
-- name    : Formalism.CohomologicalDescent.LD.cofactor_leading_minor_pow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:06:24.113091+00:00
-- url     : https://prove2.me/theorems/ad331464-3f2a-457f-9e7b-4224f7ed0b66
-- title:
--   LD: cofactor leading minor pow
-- statement:
--   The LD construction uses the cofactor leading minor pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L874-L878
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L874-L878

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

theorem Formalism.CohomologicalDescent.LD.cofactor_leading_minor_pow {r s t : ℕ} (h : s + t = r) :
    genericDet ℤ r * cofMap r (leadingMinorPolynomial r s) = genericDet ℤ r ^ s * leadingMinorPolynomial r t := by sorry
