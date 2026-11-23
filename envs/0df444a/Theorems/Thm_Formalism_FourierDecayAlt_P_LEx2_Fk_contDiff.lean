-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_Fk_contDiff
-- name    : Formalism.FourierDecayAlt.P.LEx2.Fk_contDiff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:19:40.927911+00:00
-- url     : https://prove2.me/theorems/a5116b07-09ba-4fee-becd-6afbfd8fae49
-- title:
--   LEx2: Fk cont Diff
-- statement:
--   The LEx2 construction uses the Fk cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean#L690-L695
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean#L690-L695

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem Formalism.FourierDecayAlt.P.LEx2.Fk_contDiff (k : ℕ) (s : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Fk k s) := by sorry
