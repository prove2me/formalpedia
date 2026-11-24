-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_finite_words
-- name    : Formalism.FourierDecayAlt.P.TBBx2.finite_words
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:53:43.374639+00:00
-- url     : https://prove2.me/theorems/602e1f33-9771-4b5f-a12d-a25f86c28898
-- title:
--   TBBx2: finite words
-- statement:
--   The TBBx2 construction uses the finite words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L134-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L134-L141

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2
open MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ENNReal
noncomputable section

theorem Formalism.FourierDecayAlt.P.TBBx2.finite_words {α : Type*} (A : Set α) (hA : A.Finite) (N : ℕ) :
    {w : List α | w.length ≤ N ∧ ∀ l ∈ w, l ∈ A}.Finite := by sorry
