-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_latIncl_iff_int_incl
-- name    : Formalism.CohomologicalDescent.RealLocalDeltaNabla.latIncl_iff_int_incl
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:08:24.98142+00:00
-- url     : https://prove2.me/theorems/7d7485af-aad2-4240-9061-49368ad06ea4
-- title:
--   Real Local Delta Nabla: lat Incl iff int incl
-- statement:
--   The Real Local Delta Nabla construction uses the lat Incl iff int incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/RealLocalDeltaNabla.lean#L161-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/RealLocalDeltaNabla.lean#L161-L163

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

theorem Formalism.CohomologicalDescent.RealLocalDeltaNabla.latIncl_iff_int_incl (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ)
    (hl : l.Prime) (hlO : ¬ IsUnit (l : O)) (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (e : ℕ) :
    LatIncl (l : O) (deltaIn O r n hn ν) e ↔ InclZ r n hn ν l e := by sorry
