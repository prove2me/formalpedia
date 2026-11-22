-- Prove2me | Theorems.Thm_Formalism_F_discreteTopology_of_le
-- name    : Formalism.F.discreteTopology_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:52:03.66462+00:00
-- url     : https://prove2.me/theorems/0dd947c4-fe2f-4951-9b91-75d3c0a3ae82
-- title:
--   F: discrete Topology of le
-- statement:
--   The F construction uses the discrete Topology of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/DiscreteTopologyOfLe.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/DiscreteTopologyOfLe.lean#L7-L10

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.F
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem Formalism.F.discreteTopology_of_le {L N : Submodule ℤ E} (h : N ≤ L) [hL : DiscreteTopology L] :
    DiscreteTopology N := by sorry
