-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_monomialMatrix_inv_left
-- name    : Formalism.FourierDecayAlt.P.C2x2.monomialMatrix_inv_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:18:55.635074+00:00
-- url     : https://prove2.me/theorems/68fa3dac-29e8-4e51-9cd7-9dd2a9f79e1b
-- title:
--   C2x2: monomial Matrix inv left
-- statement:
--   The C2x2 construction uses the monomial Matrix inv left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L96-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L96-L105

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

theorem Formalism.FourierDecayAlt.P.C2x2.monomialMatrix_inv_left (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) :
    C2.monoP w.symm (fun i => (d (w.symm i))⁻¹) * C2.monoP w d = 1 := by sorry
