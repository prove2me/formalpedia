-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x5_scalInv_symm_apply
-- name    : Formalism.FourierDecayAlt.P.S6x5.scalInv_symm_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:27:09.168221+00:00
-- url     : https://prove2.me/theorems/657f5324-3073-5d73-80be-2e834d209086
-- title:
--   S6x5: scal Inv symm apply
-- statement:
--   The S6x5 construction uses the scal Inv symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwistedIsRealOrderLattice.lean#L53-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwistedIsRealOrderLattice.lean#L53-L53

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x5
open Module MeasureTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem Formalism.FourierDecayAlt.P.S6x5.scalInv_symm_apply (c : ℝ) (hc : c ≠ 0) (x : V) : (scalInv V c hc).symm x = c • x := by sorry
