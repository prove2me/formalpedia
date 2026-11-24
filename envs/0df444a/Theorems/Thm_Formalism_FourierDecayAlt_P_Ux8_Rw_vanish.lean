-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_Rw_vanish
-- name    : Formalism.FourierDecayAlt.P.Ux8.Rw_vanish
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:26:06.673793+00:00
-- url     : https://prove2.me/theorems/67f86cff-10bf-4e7b-a566-66160083037e
-- title:
--   Ux8: Rw vanish
-- statement:
--   The Ux8 construction uses the Rw vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SeminormCompletion.lean#L521-L536
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SeminormCompletion.lean#L521-L536

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Rw_vanish

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux8
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.Ux8.Rw_vanish {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {O : Set (B.Mat k r)} (hO : IsOpen O)
    {f : B.Mat k r → E} (h : ∀ g ∈ O, f g = 0) (w : List (B.Mat k r)) : ∀ g ∈ O, B.Rw w f g = 0 := by sorry
