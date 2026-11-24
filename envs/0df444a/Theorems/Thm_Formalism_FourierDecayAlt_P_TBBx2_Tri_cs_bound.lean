-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Tri_cs_bound
-- name    : Formalism.FourierDecayAlt.P.TBBx2.Tri.cs_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:55:11.912895+00:00
-- url     : https://prove2.me/theorems/0cce9264-1b25-4eff-9cea-e9f54f2b7bd1
-- title:
--   Tri: cs bound
-- statement:
--   The Tri construction uses the cs bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L280-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L280-L290

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
variable {P : M.Par}

theorem Formalism.FourierDecayAlt.P.TBBx2.Tri.cs_bound {n : ℕ} (a x : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i * x i) ^ 2 ≤ (∑ i, a i) * ∑ i, a i * x i ^ 2 := by sorry
