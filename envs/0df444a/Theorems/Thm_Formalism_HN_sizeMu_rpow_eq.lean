-- Prove2me | Theorems.Thm_Formalism_HN_sizeMu_rpow_eq
-- name    : Formalism.HN.sizeMu_rpow_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:43.460172+00:00
-- url     : https://prove2.me/theorems/d74c0ada-bdd9-480b-b41c-8075a3c8a86e
-- title:
--   HN: size Mu rpow eq
-- statement:
--   The HN construction uses the size Mu rpow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SizeMu.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SizeMu.lean#L13-L22

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

theorem Formalism.HN.sizeMu_rpow_eq (f J C d : ℝ) (hf : 0 < f) (hJ : 0 < J) (hC : 0 < C) (hd : 0 < d) :
    ((2 : ℝ) ^ (f * J) * d ^ (-J / 2) * C) ^ ((1 : ℝ) / (2 * f * J)) =
      Real.exp (Real.log 2 / 2 - Real.log d / (2 * (2 * f)) - (-Real.log C) / ((2 * f) * J)) := by sorry
