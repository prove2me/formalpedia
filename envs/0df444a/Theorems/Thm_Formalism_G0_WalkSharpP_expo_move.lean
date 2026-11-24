-- Prove2me | Theorems.Thm_Formalism_G0_WalkSharpP_expo_move
-- name    : Formalism.G0.WalkSharpP.expo_move
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:33.067696+00:00
-- url     : https://prove2.me/theorems/0dba1218-fbe5-4af6-be45-41bec5338ca4
-- title:
--   Walk Sharp P: expo move
-- statement:
--   The Walk Sharp P construction uses the expo move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L281-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L281-L298

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

theorem Formalism.G0.WalkSharpP.expo_move {V : ℕ} {m : ℕ} {B : Finset (Fin V)} {i : Fin V → ℕ} {v w : Fin V}
    (hv : v ∈ B) (hiv : i v + 1 = m) (hw : (w : ℕ) = top B + 1) (hiw : i w = 0) (u : Fin V) :
    expo m (insert w (B.erase v)) (Function.update i v 0) u =
      expo m B i u + if u = v then 1 else 0 := by sorry
