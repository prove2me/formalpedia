-- Prove2me | Theorems.Thm_Formalism_HN_size_maximal_slope
-- name    : Formalism.HN.size_maximal_slope
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:35.013699+00:00
-- url     : https://prove2.me/theorems/241fe227-0ddf-404b-97c6-60014e9a04ad
-- title:
--   HN: size maximal slope
-- statement:
--   The HN construction uses the size maximal slope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SizeMu.lean#L174-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SizeMu.lean#L174-L175

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField NumberField.InfinitePlace
noncomputable section
open Formalism Formalism.HN

theorem Formalism.HN.size_maximal_slope : SizeMu := by sorry
