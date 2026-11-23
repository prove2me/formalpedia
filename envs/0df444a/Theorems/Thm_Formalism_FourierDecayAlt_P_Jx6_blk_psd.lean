-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx6_blk_psd
-- name    : Formalism.FourierDecayAlt.P.Jx6.blk_psd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:02.138505+00:00
-- url     : https://prove2.me/theorems/921e54fd-f74d-4430-b2c1-46613d7d6d31
-- title:
--   Jx6: blk psd
-- statement:
--   The Jx6 construction uses the blk psd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionGivesUniformBoundsForm.lean#L71-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionGivesUniformBoundsForm.lean#L71-L79

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

theorem Formalism.FourierDecayAlt.P.Jx6.blk_psd {E : Type} [Field E] {Y : Finset (TB.Pt E)} {S : Finset E} {s : ℕ}
    {κ : TB.Pt E → TB.Pt E → ℂ} (hκ : TB.PSDOn (TB.pts Y s S) κ) {t : E} (ht : t ∈ S) :
    TB.PSDOn Y (TB.blk κ s t t) := by sorry
