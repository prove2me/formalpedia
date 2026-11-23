-- Prove2me | Theorems.Thm_Formalism_F_slopeLeMuMax
-- name    : Formalism.F.slopeLeMuMax
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:54.781098+00:00
-- url     : https://prove2.me/theorems/a1d6a8ef-e11d-478a-8790-e3f16b6542cd
-- title:
--   F: slope Le Mu Max
-- statement:
--   The F construction uses the slope Le Mu Max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/ExistsSaturatedSlopeEqMuMax.lean#L24-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/ExistsSaturatedSlopeEqMuMax.lean#L24-L24

import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolPos
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqCovolume
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopesBdd
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeLeMuMaxOf
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeInequality
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SaturationProperties
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_FiniteSaturated
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_MuMaxAttained
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_MuMaxLeMin
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_OrthSum
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.F

theorem Formalism.F.slopeLeMuMax : SlopeLeMuMax := by sorry
