-- Prove2me | Theorems.Thm_Formalism_G0_ManyOrbitsP_geom_le
-- name    : Formalism.G0.ManyOrbitsP.geom_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:42.813719+00:00
-- url     : https://prove2.me/theorems/deed8c7e-2655-4f03-9997-d41d14fac3f1
-- title:
--   Many Orbits P: geom le
-- statement:
--   The Many Orbits P construction uses the geom le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ManyOrbits.lean#L126-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ManyOrbits.lean#L126-L133

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

theorem Formalism.G0.ManyOrbitsP.geom_le (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) (n : ℕ) :
    ∑ i ∈ Finset.range n, s ^ i ≤ 2 - 2 * s ^ n := by sorry
