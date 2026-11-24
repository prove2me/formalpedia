-- Prove2me | Theorems.Thm_Formalism_HN_degree_supermodular_integral
-- name    : Formalism.HN.degree_supermodular_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:58.103543+00:00
-- url     : https://prove2.me/theorems/0902e2b5-d352-4d35-8efa-908f24415e60
-- title:
--   HN: degree supermodular integral
-- statement:
--   The HN construction uses the degree supermodular integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DegSupermodZ.lean#L153-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DegSupermodZ.lean#L153-L282

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
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
open Formalism Formalism.HN
open Formalism.F Formalism.RankSupermodularCovolume

theorem Formalism.HN.degree_supermodular_integral : DegSupermodZ := by sorry
