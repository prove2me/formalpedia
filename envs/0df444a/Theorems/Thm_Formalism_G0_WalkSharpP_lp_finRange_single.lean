-- Prove2me | Theorems.Thm_Formalism_G0_WalkSharpP_lp_finRange_single
-- name    : Formalism.G0.WalkSharpP.lp_finRange_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:23.995021+00:00
-- url     : https://prove2.me/theorems/10ee1a7a-a208-4f80-bf7a-b3aadc2d2494
-- title:
--   Walk Sharp P: lp fin Range single
-- statement:
--   The Walk Sharp P construction uses the lp fin Range single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L63-L66

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

theorem Formalism.G0.WalkSharpP.lp_finRange_single (y : Fin V → Module.End R X) (v : Fin V) :
    lp y (List.finRange V) (fun u => if u = v then 1 else 0) = y v := by sorry
