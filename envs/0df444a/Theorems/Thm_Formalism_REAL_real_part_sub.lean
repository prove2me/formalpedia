-- Prove2me | Theorems.Thm_Formalism_REAL_real_part_sub
-- name    : Formalism.REAL.real_part_sub
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:24:36.308439+00:00
-- url     : https://prove2.me/theorems/f7a4ad1c-0bba-4cb8-8411-cbf8026b4dc6
-- title:
--   REAL: real part sub
-- statement:
--   The REAL construction uses the real part sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexifiedDerivativeCommutator.lean#L109-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexifiedDerivativeCommutator.lean#L109-L113

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.REAL.real_part_sub {n : ℕ} (ε : Fin n → Bool) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε (Z - W) = cpart1 ε Z - cpart1 ε W := by sorry
