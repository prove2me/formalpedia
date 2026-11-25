-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_norm_iteratedFDeriv_inner_self_le
-- name    : Formalism.FourierDecayAlt.P5.HerC.Fou.norm_iteratedFDeriv_inner_self_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:39:58.108165+00:00
-- url     : https://prove2.me/theorems/9522dcab-dc26-4db1-8fe4-e98ac4523aeb
-- title:
--   Fou: norm iterated FDeriv inner self le
-- statement:
--   The Fou construction uses the norm iterated FDeriv inner self le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormIteratedFDerivWithinInvOneLe.lean#L29-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormIteratedFDerivWithinInvOneLe.lean#L29-L58

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralIteratedFDerivEqZero
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormIteratedFDerivWithinInvOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Set
open scoped Nat
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerC Formalism.FourierDecayAlt.P5.HerC.Fou
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem Formalism.FourierDecayAlt.P5.HerC.Fou.norm_iteratedFDeriv_inner_self_le (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y : V => inner ℝ y y) x‖ ≤ 2 ^ n * (1 + ‖x‖) ^ 2 := by sorry
