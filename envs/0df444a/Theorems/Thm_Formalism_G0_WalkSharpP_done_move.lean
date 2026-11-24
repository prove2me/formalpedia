-- Prove2me | Theorems.Thm_Formalism_G0_WalkSharpP_done_move
-- name    : Formalism.G0.WalkSharpP.done_move
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:43:59.325094+00:00
-- url     : https://prove2.me/theorems/8a5d012d-11ee-4f93-ac75-1573ea35275b
-- title:
--   Walk Sharp P: done move
-- statement:
--   The Walk Sharp P construction uses the done move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L132-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L132-L164

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

theorem Formalism.G0.WalkSharpP.done_move {V : ℕ} {B : Finset (Fin V)} {v w u : Fin V} (hv : v ∈ B)
    (hw : (w : ℕ) = top B + 1) :
    ((u : ℕ) < top (insert w (B.erase v)) ∧ u ∉ insert w (B.erase v)) ↔
      (((u : ℕ) < top B ∧ u ∉ B) ∨ u = v) := by sorry
