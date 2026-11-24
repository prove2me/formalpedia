-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_add_fst
-- name    : Formalism.FourierDecayAlt.P5.pr_add_fst
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:27:32.292052+00:00
-- url     : https://prove2.me/theorems/390a304c-b486-4fc4-8f37-29aa15db7bfa
-- title:
--   P5: pr add fst
-- statement:
--   The P5 construction uses the pr add fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FsvMulFsvNeg.lean#L140-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FsvMulFsvNeg.lean#L140-L140

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate ContDiff
open Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem Formalism.FourierDecayAlt.P5.pr_add_fst (a b : Pr V) : (a + b).1 = a.1 + b.1 := by sorry

attribute [defeq] Formalism.FourierDecayAlt.P5.pr_add_fst
