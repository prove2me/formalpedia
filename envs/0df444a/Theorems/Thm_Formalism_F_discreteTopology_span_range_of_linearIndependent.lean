-- Prove2me | Theorems.Thm_Formalism_F_discreteTopology_span_range_of_linearIndependent
-- name    : Formalism.F.discreteTopology_span_range_of_linearIndependent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:21:49.465898+00:00
-- url     : https://prove2.me/theorems/e005ff1e-c00a-41e1-9924-b91ac5a800a7
-- title:
--   F: discrete Topology span range of linear Independent
-- statement:
--   The F construction uses the discrete Topology span range of linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/DegQuot.lean#L24-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/DegQuot.lean#L24-L68

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot
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

theorem Formalism.F.discreteTopology_span_range_of_linearIndependent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (c : ι → E) (hc : LinearIndependent ℝ c) :
    DiscreteTopology (span ℤ (Set.range c)) := by sorry
