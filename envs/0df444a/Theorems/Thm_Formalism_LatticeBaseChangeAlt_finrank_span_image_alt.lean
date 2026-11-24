-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_finrank_span_image_alt
-- name    : Formalism.LatticeBaseChangeAlt.finrank_span_image_alt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T09:52:06.242261+00:00
-- url     : https://prove2.me/theorems/d0d32a86-35f3-47db-8e7c-66f451c8ab2d
-- title:
--   Lattice Base Change Alt: finrank span image alt
-- statement:
--   The Lattice Base Change Alt construction uses the finrank span image alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LinearIndependentOfIsBaseChange.lean#L45-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LinearIndependentOfIsBaseChange.lean#L45-L58

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

theorem Formalism.LatticeBaseChangeAlt.finrank_span_image_alt : FinrankSpanImage := by sorry
