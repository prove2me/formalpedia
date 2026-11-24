-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_zero_notMem_detSet
-- name    : Formalism.FourierDecayAlt.P.Ux8.zero_notMem_detSet
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:58:43.878224+00:00
-- url     : https://prove2.me/theorems/e0afc128-7e90-4c3d-844b-fccbaadb8ffe
-- title:
--   Ux8: zero not Mem det Set
-- statement:
--   The Ux8 construction uses the zero not Mem det Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SeminormCompletion.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SeminormCompletion.lean#L11-L18

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
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

theorem Formalism.FourierDecayAlt.P.Ux8.zero_notMem_detSet (hD : G.DetMatch) (n : ℕ) (Kc : Set ℂ) (h0 : (0:ℂ) ∉ Kc) : (0:ℂ) ∉ G.detSet n Kc := by sorry
