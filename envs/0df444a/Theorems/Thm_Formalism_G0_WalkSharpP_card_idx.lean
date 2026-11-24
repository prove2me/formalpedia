-- Prove2me | Theorems.Thm_Formalism_G0_WalkSharpP_card_idx
-- name    : Formalism.G0.WalkSharpP.card_idx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:14.266273+00:00
-- url     : https://prove2.me/theorems/1ab4d89a-244e-46be-80dc-66765d6e6244
-- title:
--   Walk Sharp P: card idx
-- statement:
--   The Walk Sharp P construction uses the card idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L249-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L249-L259

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.WalkSharpP

theorem Formalism.G0.WalkSharpP.card_idx {V : ℕ} (m : ℕ) (B : Finset (Fin V)) : (idx m B).card = m ^ B.card := by sorry
