-- Prove2me | Theorems.Thm_Formalism_G0_WalkSharpP_monoOp_eq
-- name    : Formalism.G0.WalkSharpP.monoOp_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:30.642812+00:00
-- url     : https://prove2.me/theorems/f98ed06d-4550-4936-9bf7-585c8aa61730
-- title:
--   Walk Sharp P: mono Op eq
-- statement:
--   The Walk Sharp P construction uses the mono Op eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L92-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L92-L105

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

theorem Formalism.G0.WalkSharpP.monoOp_eq (π : R) (y : Fin V → Module.End R X) (m : ℕ) (S : Fin V → ℕ)
    (e : Fin V → Bool) :
    monoOp π y m S e = π ^ (∑ u, if e u then 0 else S u) •
      lp y (List.finRange V) (fun u => if e u then m else 0) := by sorry
