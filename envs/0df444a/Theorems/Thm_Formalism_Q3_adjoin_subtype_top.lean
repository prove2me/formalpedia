-- Prove2me | Theorems.Thm_Formalism_Q3_adjoin_subtype_top
-- name    : Formalism.Q3.adjoin_subtype_top
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:17:32.818961+00:00
-- url     : https://prove2.me/theorems/4eed6c7a-fec4-4215-be9e-a74114020d1a
-- title:
--   Q3: adjoin subtype top
-- statement:
--   The Q3 construction uses the adjoin subtype top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/MQGalois.lean#L122-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/MQGalois.lean#L122-L127

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.Q3

theorem Formalism.Q3.adjoin_subtype_top {L : Type} [Field L] [Algebra ℚ L] (K : IntermediateField ℚ L)
    {k : ℕ} (β : Fin k → L) (hK : K = IntermediateField.adjoin ℚ (Set.range β)) (α' : Fin k → K)
    (hα : ∀ i, (α' i : L) = β i) [inst : Algebra ℚ K] :
    IntermediateField.adjoin ℚ (Set.range α') = ⊤ := by sorry
