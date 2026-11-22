-- Prove2me | Theorems.Thm_Formalism_F_att_rk_pos
-- name    : Formalism.F.att_rk_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:27.027154+00:00
-- url     : https://prove2.me/theorems/a7252e2f-f597-4ed3-86d0-353b8603334e
-- title:
--   F: att rk pos
-- statement:
--   The F construction uses the att rk pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/MuMaxAttained.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/MuMaxAttained.lean#L13-L15

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

theorem Formalism.F.att_rk_pos {N : Submodule ℤ E} [DiscreteTopology N] (hN : N ≠ ⊥) : 0 < rk N := by sorry
