-- Prove2me | Theorems.Thm_Formalism_HN_theoremFSharp_of
-- name    : Formalism.HN.theoremFSharp_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:57.31287+00:00
-- url     : https://prove2.me/theorems/5612d5c0-7c43-4a0f-b087-d5585cdf2ca1
-- title:
--   HN: theorem FSharp of
-- statement:
--   The HN construction uses the theorem FSharp of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean#L168-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean#L168-L386

import Definitions.Def_Formalism_HarderNarasimhan_StatementFrameF
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameHermSharpB
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameLinearAlgebraFirst
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TheoremFSharp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset Formalism.CorankShareLayerCake.FR
noncomputable section
open Formalism Formalism.HN
set_option maxHeartbeats 4000000

theorem Formalism.HN.theoremFSharp_of (hLA : FrameLA1) : TheoremFSharp := by sorry
