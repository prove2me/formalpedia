-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_bt_mul_diag
-- name    : Formalism.FourierDecayAlt.P.C2x2.bt_mul_diag
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:59:21.729304+00:00
-- url     : https://prove2.me/theorems/7364c7a9-9bc0-4a3f-840c-1f52ce2a3cc2
-- title:
--   C2x2: bt mul diag
-- statement:
--   The C2x2 construction uses the bt mul diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L19-L27

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
open Formalism.FourierDecayAlt.P.C2x2
variable {m : ℕ}

theorem Formalism.FourierDecayAlt.P.C2x2.bt_mul_diag {α : Type*} [LinearOrder α] {b : Fin m → α} (hb : Function.Injective b)
    {M N : Matrix (Fin m) (Fin m) ℂ} (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) (i : Fin m) :
    (M * N) i i = M i i * N i i := by sorry
