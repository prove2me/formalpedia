-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HilbertSchmidtVectorization_adjH_spec
-- name    : Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization.adjH_spec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:15:22.260943+00:00
-- url     : https://prove2.me/theorems/275fa71c-5c23-43a6-ad35-ad50ff824c57
-- title:
--   Hilbert Schmidt Vectorization: adj H spec
-- statement:
--   The Hilbert Schmidt Vectorization construction uses the adj H spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HsVecApply.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HsVecApply.lean#L62-L65

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

theorem Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization.adjH_spec (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (A B : Wq →L[ℂ] Wp) :
    hsInner (T A) B = hsInner A (adjH T B) := by sorry
