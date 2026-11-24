-- Prove2me | Theorems.Thm_Formalism_G0_TailConcavityP_choose_cast
-- name    : Formalism.G0.TailConcavityP.choose_cast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:17.894032+00:00
-- url     : https://prove2.me/theorems/b02ec268-cb86-4dd0-ae08-09883a9eafe3
-- title:
--   Tail Concavity P: choose cast
-- statement:
--   The Tail Concavity P construction uses the choose cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailConcavity.lean#L14-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailConcavity.lean#L14-L30

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailConcavity
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
open Finset
open Formalism Formalism.G0
open Formalism.G0.TailConcavityP

theorem Formalism.G0.TailConcavityP.choose_cast (y k : ℕ) :
    ((y + k).choose k : ℝ) = ∏ i ∈ range k, (((y : ℝ) + i + 1) / (i + 1)) := by sorry
