-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Tri_hsVec_sum
-- name    : Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_sum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:54:47.073076+00:00
-- url     : https://prove2.me/theorems/2208fcfd-ac58-4d0e-8814-1613cdad497e
-- title:
--   Tri: hs Vec sum
-- statement:
--   The Tri construction uses the hs Vec sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L256-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L256-L260

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2 Formalism.FourierDecayAlt.P.TBBx2.Tri
open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB
open scoped ENNReal
noncomputable section
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_sum {n : ℕ} (A : Fin n → Wq →L[ℂ] Wp) (s : Finset (Fin n)) :
    B.hsVec (∑ i ∈ s, A i) = ∑ i ∈ s, B.hsVec (A i) := by sorry
