-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HilbertSchmidtVectorization_conjE_hsVec
-- name    : Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization.conjE_hsVec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:15:04.000979+00:00
-- url     : https://prove2.me/theorems/d27a285b-53b9-46fd-93c7-49216637357f
-- title:
--   Hilbert Schmidt Vectorization: conj E hs Vec
-- statement:
--   The Hilbert Schmidt Vectorization construction uses the conj E hs Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HsVecApply.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HsVecApply.lean#L57-L60

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsVecApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization.conjE_hsVec (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (A : Wq →L[ℂ] Wp) :
    conjE T (hsVec A) = hsVec (T A) := by sorry
