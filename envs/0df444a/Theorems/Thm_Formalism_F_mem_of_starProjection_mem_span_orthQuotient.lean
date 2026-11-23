-- Prove2me | Theorems.Thm_Formalism_F_mem_of_starProjection_mem_span_orthQuotient
-- name    : Formalism.F.mem_of_starProjection_mem_span_orthQuotient
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:52.412803+00:00
-- url     : https://prove2.me/theorems/d2af3fca-6f42-4681-b159-8dcfcc14ac11
-- title:
--   F: mem of star Projection mem span orth Quotient
-- statement:
--   The F construction uses the mem of star Projection mem span orth Quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/FiniteSaturated.lean#L36-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/FiniteSaturated.lean#L36-L50

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

theorem Formalism.F.mem_of_starProjection_mem_span_orthQuotient {L M N₁ : Submodule ℤ E} (hM : IsSaturated L M) (h1 : N₁ ≤ M)
    {x : E} (hx : x ∈ L)
    (hπ : (span ℝ (N₁ : Set E))ᗮ.starProjection x ∈ span ℝ (quot M N₁ : Set E)) : x ∈ M := by sorry
