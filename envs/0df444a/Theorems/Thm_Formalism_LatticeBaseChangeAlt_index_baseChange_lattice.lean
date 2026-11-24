-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_index_baseChange_lattice
-- name    : Formalism.LatticeBaseChangeAlt.index_baseChange_lattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:30.143973+00:00
-- url     : https://prove2.me/theorems/77af8eef-a9c9-4aba-925f-6b8f170264af
-- title:
--   Lattice Base Change Alt: index base Change lattice
-- statement:
--   The Lattice Base Change Alt construction uses the index base Change lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LatticeIndexBis.lean#L183-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LatticeIndexBis.lean#L183-L270

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LatticeIndexBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module

theorem Formalism.LatticeBaseChangeAlt.index_baseChange_lattice : RelIndexSpanImage := by sorry
