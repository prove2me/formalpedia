-- Prove2me | Theorems.Thm_Formalism_HN_hilbert_schmidt_zero_map
-- name    : Formalism.HN.hilbert_schmidt_zero_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:21.003686+00:00
-- url     : https://prove2.me/theorems/39035521-06c5-40d9-aaaa-e8236c0b074c
-- title:
--   HN: hilbert schmidt zero map
-- statement:
--   The HN construction uses the hilbert schmidt zero map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean#L161-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean#L161-L164

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

theorem Formalism.HN.hilbert_schmidt_zero_map {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (c : ℝ) : hs2 (frK c (0 : E →ₗ[ℂ] F) - LinearMap.id) = finrank ℂ E := by sorry
