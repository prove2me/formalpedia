-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_map_cast_image_val_eq
-- name    : Formalism.CohomologicalDescent.map_cast_image_val_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:37:55.021845+00:00
-- url     : https://prove2.me/theorems/1d1f4830-9f63-4cc3-9569-4bd21c9222f8
-- title:
--   Cohomological Descent: map cast image val eq
-- statement:
--   The Cohomological Descent construction uses the map cast image val eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightExchangeChainHolds.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightExchangeChainHolds.lean#L12-L16

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_WEChain
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ContentLinkageHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightExchangeBoundHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightExchangeChainHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open Formalism Formalism.CohomologicalDescent

theorem Formalism.CohomologicalDescent.map_cast_image_val_eq (l N : ℕ) (W : Fin N → ℤ) (hW : StrictAnti W) :
    Multiset.map (fun u : ℤ => (u : ZMod l)) (Finset.univ.image W).val =
      Multiset.map (fun a => ((W a : ℤ) : ZMod l)) Finset.univ.val := by sorry
