-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_star_mkP
-- name    : Formalism.FourierDecayAlt.P5.star_mkP
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:57:13.087802+00:00
-- url     : https://prove2.me/theorems/60d3b9f3-2e59-4c59-835f-1e18ef2dfb93
-- title:
--   P5: star mk P
-- statement:
--   The P5 construction uses the star mk P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtFsvOther.lean#L238-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtFsvOther.lean#L238-L238

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

theorem Formalism.FourierDecayAlt.P5.star_mkP (A B : Module.End ℂ V) : star (mkP A B : Pr V) = mkP B A := by sorry
