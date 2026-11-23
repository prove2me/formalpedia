-- Prove2me | Theorems.Thm_Formalism_F_muMaxLeMin_of
-- name    : Formalism.F.muMaxLeMin_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:41.614405+00:00
-- url     : https://prove2.me/theorems/59038181-d5c9-43d1-8509-271e3f8f3786
-- title:
--   F: mu Max Le Min of
-- statement:
--   The F construction uses the mu Max Le Min of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/MuMaxLeMin.lean#L11-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/MuMaxLeMin.lean#L11-L38

import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_MuMaxAttained
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_MuMaxLeMin
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

theorem Formalism.F.muMaxLeMin_of (hP : CovolPos.{u}) (hS : ShortVector.{u}) : MuMaxLeMin.{u} := by sorry
