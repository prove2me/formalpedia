-- Prove2me | Theorems.Thm_Formalism_HN_sizeMu_finrank_eq
-- name    : Formalism.HN.sizeMu_finrank_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:28.020835+00:00
-- url     : https://prove2.me/theorems/886f620b-d97f-4166-b91a-9e7ec0fd6a4d
-- title:
--   HN: size Mu finrank eq
-- statement:
--   The HN construction uses the size Mu finrank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SizeMu.lean#L24-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SizeMu.lean#L24-L37

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

theorem Formalism.HN.sizeMu_finrank_eq (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] :
    Module.finrank ℚ K = 2 * nPl K := by sorry
