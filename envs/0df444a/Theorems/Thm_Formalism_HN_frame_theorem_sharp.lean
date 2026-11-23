-- Prove2me | Theorems.Thm_Formalism_HN_frame_theorem_sharp
-- name    : Formalism.HN.frame_theorem_sharp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:56.736891+00:00
-- url     : https://prove2.me/theorems/b94a8971-aab2-4890-a01a-af4a602f70a4
-- title:
--   HN: frame theorem sharp
-- statement:
--   The HN construction uses the frame theorem sharp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean#L388-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean#L388-L388

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

theorem Formalism.HN.frame_theorem_sharp : TheoremFSharp := by sorry
