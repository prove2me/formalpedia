-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_c2x2_simpleLow_succ
-- name    : Formalism.FourierDecayAlt.P.c2x2_simpleLow_succ
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:36:18.830324+00:00
-- url     : https://prove2.me/theorems/76e44102-914d-4d38-b04c-9fb10e7fc24b
-- title:
--   P: c2x2 simple Low succ
-- statement:
--   The P construction uses the c2x2 simple Low succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L167-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L167-L173

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2

theorem Formalism.FourierDecayAlt.P.c2x2_simpleLow_succ {n : ℕ} (l : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    C2.simpleLow l = ∑ a : Fin n, l a.succ a.castSucc := by sorry
