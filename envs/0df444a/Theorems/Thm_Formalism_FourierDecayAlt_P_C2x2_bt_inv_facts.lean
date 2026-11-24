-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_bt_inv_facts
-- name    : Formalism.FourierDecayAlt.P.C2x2.bt_inv_facts
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:18:28.943258+00:00
-- url     : https://prove2.me/theorems/7c1c7a61-32b1-4b97-90f0-2f9976413e16
-- title:
--   C2x2: bt inv facts
-- statement:
--   The C2x2 construction uses the bt inv facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L29-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L29-L37

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

theorem Formalism.FourierDecayAlt.P.C2x2.bt_inv_facts {α : Type*} [LinearOrder α] {b : Fin m → α} (hb : Function.Injective b)
    {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.BlockTriangular b) (hd : ∀ i, M i i = 1) (hu : IsUnit M.det) :
    M⁻¹.BlockTriangular b ∧ ∀ i, M⁻¹ i i = 1 := by sorry
