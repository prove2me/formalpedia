-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx6_psd_pull
-- name    : Formalism.FourierDecayAlt.P.Jx6.psd_pull
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:48:01.808808+00:00
-- url     : https://prove2.me/theorems/2a40defa-dddf-40f2-af1f-f61039e33213
-- title:
--   Jx6: psd pull
-- statement:
--   The Jx6 construction uses the psd pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionGivesUniformBoundsForm.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionGivesUniformBoundsForm.lean#L13-L18

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionGivesUniformBoundsForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx6

theorem Formalism.FourierDecayAlt.P.Jx6.psd_pull {α β : Type} {G : Finset β} {F : Finset α} (f : G → F) {k : α → α → ℂ}
    {k' : β → β → ℂ} (h : ∀ x y : G, k' x y = k (f x) (f y)) (hk : TB.PSDOn F k) : TB.PSDOn G k' := by sorry
