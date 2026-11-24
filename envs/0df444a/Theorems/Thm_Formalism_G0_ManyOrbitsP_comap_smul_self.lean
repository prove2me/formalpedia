-- Prove2me | Theorems.Thm_Formalism_G0_ManyOrbitsP_comap_smul_self
-- name    : Formalism.G0.ManyOrbitsP.comap_smul_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:23.171801+00:00
-- url     : https://prove2.me/theorems/fe172176-f563-4d74-8170-d7ada3a1575c
-- title:
--   Many Orbits P: comap smul self
-- statement:
--   The Many Orbits P construction uses the comap smul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ManyOrbits.lean#L118-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ManyOrbits.lean#L118-L122

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

theorem Formalism.G0.ManyOrbitsP.comap_smul_self (I : Ideal R) (M : Submodule R X) :
    (I • M).comap M.subtype = I • (⊤ : Submodule R M) := by sorry
