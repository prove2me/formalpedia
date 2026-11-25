-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_hasWt2_iff
-- name    : Formalism.BaseCaseIdentities.hasWt2_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:50:33.191647+00:00
-- url     : https://prove2.me/theorems/7bf8416b-50ba-447d-a569-bbc8448afbe2
-- title:
--   Base Case Identities: has Wt2 iff
-- statement:
--   The Base Case Identities construction uses the has Wt2 iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/BaseCaseFalseGeneralHolds.lean#L71-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/BaseCaseFalseGeneralHolds.lean#L71-L92

import Definitions.Def_Formalism_FrobeniusBaseCase_CoeffOfFirstMultiplier
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
variable {k : Type*} [Field k] {Z Z' : Type*} {v : AddValuation k (WithTop ℝ)}

theorem Formalism.BaseCaseIdentities.hasWt2_iff {r r' w : ℝ} {f : MvPowerSeries (Z ⊕ Z') k} :
    HasWt2 v r r' w f ↔ HasWtG v (om2 Z Z' r r') w f := by sorry
