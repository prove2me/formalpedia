-- Prove2me | Theorems.Thm_Formalism_G0_ManyOrbitsP_fact_esymm_le
-- name    : Formalism.G0.ManyOrbitsP.fact_esymm_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:01.026815+00:00
-- url     : https://prove2.me/theorems/594a4b8f-ca2e-4c1e-87a0-e8d6e1ffbc33
-- title:
--   Many Orbits P: fact esymm le
-- statement:
--   The Many Orbits P construction uses the fact esymm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ManyOrbits.lean#L28-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ManyOrbits.lean#L28-L56

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

theorem Formalism.G0.ManyOrbitsP.fact_esymm_le (s : Multiset ℝ) (hs : ∀ x ∈ s, 0 ≤ x) (n : ℕ) :
    (n.factorial : ℝ) * s.esymm n ≤ s.sum ^ n := by sorry
