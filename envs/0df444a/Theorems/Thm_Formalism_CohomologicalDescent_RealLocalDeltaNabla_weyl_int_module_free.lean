-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_weyl_int_module_free
-- name    : Formalism.CohomologicalDescent.RealLocalDeltaNabla.weyl_int_module_free
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:08:38.940862+00:00
-- url     : https://prove2.me/theorems/fd09d338-3fb3-4854-b64c-2ff47932ddb1
-- title:
--   Real Local Delta Nabla: weyl int module free
-- statement:
--   The Real Local Delta Nabla construction uses the weyl int module free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/RealLocalDeltaNabla.lean#L479-L485
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/RealLocalDeltaNabla.lean#L479-L485

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.RealLocalDeltaNabla
open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA Formalism.CohomologicalDescent.SL2BinomialLattices

theorem Formalism.CohomologicalDescent.RealLocalDeltaNabla.weyl_int_module_free (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    Module.Free ℤ (weyl ℤ r n hn ν) := by sorry
