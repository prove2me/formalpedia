-- Prove2me | Theorems.Thm_Formalism_G0_WalkSharpP_expo_step
-- name    : Formalism.G0.WalkSharpP.expo_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:19.032041+00:00
-- url     : https://prove2.me/theorems/fea39ecc-74b4-4bcb-a4db-9fb658d4727f
-- title:
--   Walk Sharp P: expo step
-- statement:
--   The Walk Sharp P construction uses the expo step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L261-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L261-L269

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

theorem Formalism.G0.WalkSharpP.expo_step {V : ℕ} (m : ℕ) {B : Finset (Fin V)} (i : Fin V → ℕ) {v : Fin V}
    (hv : v ∈ B) (u : Fin V) :
    expo m B (Function.update i v (i v + 1)) u = expo m B i u + if u = v then 1 else 0 := by sorry
