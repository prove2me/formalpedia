-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LeftToRightConversion_L_to_R
-- name    : Formalism.FourierDecayAlt.P.LeftToRightConversion.L_to_R
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:25:55.510039+00:00
-- url     : https://prove2.me/theorems/b4730460-8acd-4d7f-9b73-bd74b89afc8c
-- title:
--   Left To Right Conversion: L to R
-- statement:
--   The Left To Right Conversion construction uses the L to R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftToRightConversion.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftToRightConversion.lean#L37-L44

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftToRightConversion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LeftToRightConversion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
  Formalism.FourierDecayAlt.P.ListSumInequalities Formalism.FourierDecayAlt.P.ListSumSplittings
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.LeftToRightConversion.L_to_R {H : Mat k r → E} {X g : Mat k r} (hX : inLie k r X) (hH : CkOn ((1 : ℕ) : ℕ∞) (GV k r) H)
    (hg : g ∈ GV k r) : op true X H g = ∑ i, cT i X g • op false (Lt i) H g := by sorry
