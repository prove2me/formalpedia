-- Prove2me | Theorems.Thm_Formalism_F_discreteTopology_span_singleton
-- name    : Formalism.F.discreteTopology_span_singleton
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:28.589182+00:00
-- url     : https://prove2.me/theorems/b628dddf-2bf8-4ac1-83cc-b665b7319c7c
-- title:
--   F: discrete Topology span singleton
-- statement:
--   The F construction uses the discrete Topology span singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/CovolPos.lean#L61-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/CovolPos.lean#L61-L82

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolPos
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

theorem Formalism.F.discreteTopology_span_singleton {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v : E} (hv : v ≠ 0) :
    DiscreteTopology (span ℤ ({v} : Set E)) := by sorry
