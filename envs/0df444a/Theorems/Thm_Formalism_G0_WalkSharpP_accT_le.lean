-- Prove2me | Theorems.Thm_Formalism_G0_WalkSharpP_accT_le
-- name    : Formalism.G0.WalkSharpP.accT_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:31.852137+00:00
-- url     : https://prove2.me/theorems/f36ba278-5281-40a0-b70d-c5a2845d4415
-- title:
--   Walk Sharp P: acc T le
-- statement:
--   The Walk Sharp P construction uses the acc T le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L326-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L326-L338

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

theorem Formalism.G0.WalkSharpP.accT_le {V : ℕ} (a b c : Fin V → ℕ) (m c₀ : ℕ) {B : Finset (Fin V)}
    {i : Fin V → ℕ} (hi : ∀ u ∈ B, i u < m) (u : Fin V) :
    accT a b c m c₀ B i u ≤ a u + b u + (m - 1) * c u + m * c₀ := by sorry
