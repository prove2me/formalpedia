-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_mkP_coeff
-- name    : Formalism.FourierDecayAlt.P.LEx1.mkP_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:02:27.674809+00:00
-- url     : https://prove2.me/theorems/f4ab4cb8-7108-4270-8e9b-d23158c02f24
-- title:
--   LEx1: mk P coeff
-- statement:
--   The LEx1 construction uses the mk P coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LemmaEprimeFromSteps.lean#L163-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LemmaEprimeFromSteps.lean#L163-L164

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
open Polynomial

theorem Formalism.FourierDecayAlt.P.LEx1.mkP_coeff (m : ℕ) (c : ℕ → ℂ) (k : ℕ) : (mkP m c).coeff k = if k < m + 1 then c k else 0 := by sorry
