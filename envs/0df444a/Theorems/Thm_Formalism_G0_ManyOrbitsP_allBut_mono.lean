-- Prove2me | Theorems.Thm_Formalism_G0_ManyOrbitsP_allBut_mono
-- name    : Formalism.G0.ManyOrbitsP.allBut_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:10.241804+00:00
-- url     : https://prove2.me/theorems/095db79d-c407-4906-83b1-86e9feac9c62
-- title:
--   Many Orbits P: all But mono
-- statement:
--   The Many Orbits P construction uses the all But mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ManyOrbits.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ManyOrbits.lean#L81-L86

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
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
open Formalism.G0.ManyOrbitsP
variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]

theorem Formalism.G0.ManyOrbitsP.allBut_mono {π : R} {M P : Submodule R X} {g g' E E' : ℕ} (h : AllButLE π M P g E)
    (hg : g ≤ g') (hE : E ≤ E') : AllButLE π M P g' E' := by sorry
