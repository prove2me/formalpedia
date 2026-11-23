-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx6_Nst_nonneg
-- name    : Formalism.FourierDecayAlt.P.Jx6.Nst_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:47.199942+00:00
-- url     : https://prove2.me/theorems/cc409978-74c3-41c7-ada0-c99727c29c05
-- title:
--   Jx6: Nst nonneg
-- statement:
--   The Jx6 construction uses the Nst nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionGivesUniformBoundsForm.lean#L59-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionGivesUniformBoundsForm.lean#L59-L69

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

theorem Formalism.FourierDecayAlt.P.Jx6.Nst_nonneg {E W : Type} [Field E] (D : TB.Data E W) (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ}
    (hε : 0 < ε) (i s : ℕ) (w : W) (Y : Finset (TB.Pt E)) {κ : TB.Pt E → TB.Pt E → ℂ}
    (hκ : TB.PSDOn Y κ) (t : E) : 0 ≤ (D.Nst ε i s w Y κ t t).re := by sorry
