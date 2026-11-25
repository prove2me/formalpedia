-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_star_mem_cenW
-- name    : Formalism.FourierDecayAlt.P5.star_mem_cenW
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:59:06.6278+00:00
-- url     : https://prove2.me/theorems/42c22c06-0944-514d-ac15-7ef5830cafd6
-- title:
--   P5: star mem cen W
-- statement:
--   The P5 construction uses the star mem cen W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtFsvOther.lean#L258-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtFsvOther.lean#L258-L268

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtFsvOther
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
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem Formalism.FourierDecayAlt.P5.star_mem_cenW {Wv Wv' : Module.End ℂ V} {x : Pr V} (hx : x ∈ cenW Wv Wv') : star x ∈ cenW Wv Wv' := by sorry
