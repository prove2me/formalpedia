-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_prod_mu_toZMod_val_eq_prod_Ioo
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.prod_mu_toZMod_val_eq_prod_Ioo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:25.417967+00:00
-- url     : https://prove2.me/theorems/f0e00995-292d-4e7d-9197-4d91ecafde32
-- title:
--   Height Descent Minors: prod mu to ZMod val eq prod Ioo
-- statement:
--   The Height Descent Minors construction uses the prod mu to ZMod val eq prod Ioo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L636-L657
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L636-L657

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
variable (l : ℕ) [Fact l.Prime]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.prod_mu_toZMod_val_eq_prod_Ioo (hm : MuFacts) {M : Type} [CommMonoid M] (G : ℕ → M) :
    ∏ d ∈ mu l, G (PadicInt.toZMod d).val = ∏ c ∈ Finset.Ioo 0 l, G c := by sorry
