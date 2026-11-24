-- Prove2me | Theorems.Thm_Formalism_G0_WalkSharpP_mem_idx
-- name    : Formalism.G0.WalkSharpP.mem_idx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:33.621806+00:00
-- url     : https://prove2.me/theorems/81281068-0623-449b-9780-0c4a8a9b37d6
-- title:
--   Walk Sharp P: mem idx
-- statement:
--   The Walk Sharp P construction uses the mem idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L242-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L242-L247

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

theorem Formalism.G0.WalkSharpP.mem_idx {V : ℕ} {m : ℕ} {B : Finset (Fin V)} {i : Fin V → ℕ} :
    i ∈ idx m B ↔ ∀ u, (u ∈ B → i u < m) ∧ (u ∉ B → i u = 0) := by sorry
