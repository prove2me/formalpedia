-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx6_sum_nonneg_of_psd
-- name    : Formalism.FourierDecayAlt.P.Jx6.sum_nonneg_of_psd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:47.12627+00:00
-- url     : https://prove2.me/theorems/97abc5fc-7578-474f-b794-3e7a4beaf4fd
-- title:
--   Jx6: sum nonneg of psd
-- statement:
--   The Jx6 construction uses the sum nonneg of psd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionGivesUniformBoundsForm.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionGivesUniformBoundsForm.lean#L30-L37

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

theorem Formalism.FourierDecayAlt.P.Jx6.sum_nonneg_of_psd {α : Type} {F : Finset α} {k : α → α → ℂ} (hk : TB.PSDOn F k) :
    0 ≤ (∑ x ∈ F, ∑ y ∈ F, k x y).re := by sorry
