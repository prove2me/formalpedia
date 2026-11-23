-- Prove2me | Theorems.Thm_Formalism_F_sub_mem_of_starProjection_eq
-- name    : Formalism.F.sub_mem_of_starProjection_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:53.684248+00:00
-- url     : https://prove2.me/theorems/cae2020b-a668-4885-bf74-d7ed98ad047b
-- title:
--   F: sub mem of star Projection eq
-- statement:
--   The F construction uses the sub mem of star Projection eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/FiniteSaturated.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/FiniteSaturated.lean#L30-L34

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolPos
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SaturationProperties
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_MuMaxAttained
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_FiniteSaturated
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
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem Formalism.F.sub_mem_of_starProjection_eq (W : Submodule ℝ E) {x z : E}
    (h : Wᗮ.starProjection x = Wᗮ.starProjection z) : x - z ∈ W := by sorry
