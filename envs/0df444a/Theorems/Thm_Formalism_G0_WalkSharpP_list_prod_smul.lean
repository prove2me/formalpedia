-- Prove2me | Theorems.Thm_Formalism_G0_WalkSharpP_list_prod_smul
-- name    : Formalism.G0.WalkSharpP.list_prod_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:35.39539+00:00
-- url     : https://prove2.me/theorems/aea3a305-eb02-401d-ad5f-68b6f15afd16
-- title:
--   Walk Sharp P: list prod smul
-- statement:
--   The Walk Sharp P construction uses the list prod smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L83-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L83-L90

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

theorem Formalism.G0.WalkSharpP.list_prod_smul (l : List (Fin V)) (r : Fin V → R) (A : Fin V → Module.End R X) :
    (l.map fun u => r u • A u).prod = (l.map r).prod • (l.map A).prod := by sorry
