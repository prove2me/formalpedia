-- Prove2me | Theorems.Thm_Formalism_G0_WalkSharpP_lp_single
-- name    : Formalism.G0.WalkSharpP.lp_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:21.06408+00:00
-- url     : https://prove2.me/theorems/5dd24704-78ed-48fe-b065-1808cc3f5d3a
-- title:
--   Walk Sharp P: lp single
-- statement:
--   The Walk Sharp P construction uses the lp single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L48-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L48-L61

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
variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {V : ℕ}

theorem Formalism.G0.WalkSharpP.lp_single (y : Fin V → Module.End R X) (v : Fin V) (l : List (Fin V)) (hl : l.Nodup) :
    lp y l (fun u => if u = v then 1 else 0) = if v ∈ l then y v else 1 := by sorry
