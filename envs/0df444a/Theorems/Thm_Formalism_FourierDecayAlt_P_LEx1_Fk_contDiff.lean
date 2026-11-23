-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_Fk_contDiff
-- name    : Formalism.FourierDecayAlt.P.LEx1.Fk_contDiff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:15.002458+00:00
-- url     : https://prove2.me/theorems/6218e9e0-6aed-44c8-a4dc-467940ff58d9
-- title:
--   LEx1: Fk cont Diff
-- statement:
--   The LEx1 construction uses the Fk cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LemmaEprimeFromSteps.lean#L691-L696
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LemmaEprimeFromSteps.lean#L691-L696

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem Formalism.FourierDecayAlt.P.LEx1.Fk_contDiff (k : ℕ) (s : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Fk k s) := by sorry
