-- Prove2me | Theorems.Thm_Formalism_F_att_rk_le
-- name    : Formalism.F.att_rk_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:21:31.402323+00:00
-- url     : https://prove2.me/theorems/e26ad47b-2a4d-4519-9824-6150e6b24e3d
-- title:
--   F: att rk le
-- statement:
--   The F construction uses the att rk le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/MuMaxAttained.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/MuMaxAttained.lean#L17-L18

import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_MuMaxAttained
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.F
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem Formalism.F.att_rk_le {L N : Submodule ℤ E} [DiscreteTopology L] (h : N ≤ L) : rk N ≤ rk L := by sorry
