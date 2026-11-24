-- Prove2me | Theorems.Thm_Formalism_G0_WalkSharpP_accT_move
-- name    : Formalism.G0.WalkSharpP.accT_move
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:05.970814+00:00
-- url     : https://prove2.me/theorems/5e760d5c-113b-4017-a172-91300b33bb57
-- title:
--   Walk Sharp P: acc T move
-- statement:
--   The Walk Sharp P construction uses the acc T move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L300-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L300-L324

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

theorem Formalism.G0.WalkSharpP.accT_move {V : ℕ} (a b c : Fin V → ℕ) {m c₀ : ℕ} {B : Finset (Fin V)}
    {i : Fin V → ℕ} {v w : Fin V}
    (hv : v ∈ B) (hiv : i v + 1 = m) (hw : (w : ℕ) = top B + 1) (hiw : i w = 0) (u : Fin V) :
    accT a b c m c₀ (insert w (B.erase v)) (Function.update i v 0) u =
      accT a b c m c₀ B i u + (if u = v then a v + c₀ else 0) + (if u = w then b w else 0) := by sorry
