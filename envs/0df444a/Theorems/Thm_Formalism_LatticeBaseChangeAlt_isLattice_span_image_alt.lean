-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_isLattice_span_image_alt
-- name    : Formalism.LatticeBaseChangeAlt.isLattice_span_image_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:41:02.329679+00:00
-- url     : https://prove2.me/theorems/58b65c1d-36ac-480a-94c6-c59a8bceb064
-- title:
--   Lattice Base Change Alt: is Lattice span image alt
-- statement:
--   The Lattice Base Change Alt construction uses the is Lattice span image alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LinearIndependentOfIsBaseChange.lean#L60-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LinearIndependentOfIsBaseChange.lean#L60-L105

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LinearIndependentOfIsBaseChange
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

theorem Formalism.LatticeBaseChangeAlt.isLattice_span_image_alt : IsLatticeSpanImage := by sorry
