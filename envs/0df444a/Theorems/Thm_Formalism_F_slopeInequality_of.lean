-- Prove2me | Theorems.Thm_Formalism_F_slopeInequality_of
-- name    : Formalism.F.slopeInequality_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:03.442878+00:00
-- url     : https://prove2.me/theorems/0842f170-3a47-4b61-b916-90275d4e8ac3
-- title:
--   F: slope Inequality of
-- statement:
--   The F construction uses the slope Inequality of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/SlopeInequality.lean#L111-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/SlopeInequality.lean#L111-L191

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeInequality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
universe u v

theorem Formalism.F.slopeInequality_of (h : SlopeLeMuMax.{v}) : SlopeInequality.{u, v} := by sorry
