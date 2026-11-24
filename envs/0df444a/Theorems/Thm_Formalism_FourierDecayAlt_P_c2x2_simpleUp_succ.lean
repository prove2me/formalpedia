-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_c2x2_simpleUp_succ
-- name    : Formalism.FourierDecayAlt.P.c2x2_simpleUp_succ
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:52:47.682482+00:00
-- url     : https://prove2.me/theorems/4a0d20e8-013a-4e80-bd8c-39014d7b9d71
-- title:
--   P: c2x2 simple Up succ
-- statement:
--   The P construction uses the c2x2 simple Up succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L175-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L175-L181

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

theorem Formalism.FourierDecayAlt.P.c2x2_simpleUp_succ {n : ℕ} (u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    C2.simpleUp u = ∑ a : Fin n, u a.castSucc a.succ := by sorry
