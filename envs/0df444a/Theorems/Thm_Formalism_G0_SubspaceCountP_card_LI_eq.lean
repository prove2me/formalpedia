-- Prove2me | Theorems.Thm_Formalism_G0_SubspaceCountP_card_LI_eq
-- name    : Formalism.G0.SubspaceCountP.card_LI_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:13.412806+00:00
-- url     : https://prove2.me/theorems/357db356-c92e-434f-95c6-2b4b94c3eed5
-- title:
--   Subspace Count P: card LI eq
-- statement:
--   The Subspace Count P construction uses the card LI eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/SubspaceCount.lean#L110-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/SubspaceCount.lean#L110-L120

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
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
open Module
open Formalism Formalism.G0
open Formalism.G0.SubspaceCountP
variable {F W : Type} [Field F] [Fintype F] [AddCommGroup W] [Module F W] [Finite W]

theorem Formalism.G0.SubspaceCountP.card_LI_eq (k : ℕ) :
    Nat.card (LI F W k) =
      Nat.card (Gr F W k) * ∏ i : Fin k, (Fintype.card F ^ k - Fintype.card F ^ i.val) := by sorry
