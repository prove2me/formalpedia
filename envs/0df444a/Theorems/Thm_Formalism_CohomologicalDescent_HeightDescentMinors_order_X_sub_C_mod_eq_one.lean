-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_order_X_sub_C_mod_eq_one
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.order_X_sub_C_mod_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:16.829642+00:00
-- url     : https://prove2.me/theorems/bdc905b7-ee24-416e-aabd-0adabd80b589
-- title:
--   Height Descent Minors: order X sub C mod eq one
-- statement:
--   The Height Descent Minors construction uses the order X sub C mod eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1676-L1682
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1676-L1682

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {O : Type} [CommRing O] [IsDomain O] (I : Ideal O) [IsAdicComplete I O] (c : O)

theorem Formalism.CohomologicalDescent.HeightDescentMinors.order_X_sub_C_mod_eq_one (hc : c ∈ I) :
    ((((Polynomial.X - Polynomial.C c : Polynomial O) : O⟦X⟧).map
      (Ideal.Quotient.mk I)).order.toNat) = 1 := by sorry
