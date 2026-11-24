-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DeterminantVectorSums_detVecR
-- name    : Formalism.FourierDecayAlt.P.DeterminantVectorSums.detVecR
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:31:13.021194+00:00
-- url     : https://prove2.me/theorems/2bb00875-7155-4853-9825-bd0f2e1622c1
-- title:
--   Determinant Vector Sums: det Vec R
-- statement:
--   The Determinant Vector Sums construction uses the det Vec R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StarSumLemmas.lean#L38-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StarSumLemmas.lean#L38-L53

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StarSumLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DeterminantVectorSums
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {A : Type} [Ring A] [Algebra ℂ A] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → A)

theorem Formalism.FourierDecayAlt.P.DeterminantVectorSums.detVecR (hE : GlRel E) (y : Fin (N + 1) → A) (hy : IsVec E y) (w : ℂ) (j : Fin (N + 1)) :
    qdet E w * y j = y j * qdet E w - ∑ l, Tch E (w - 1) j l * y l := by sorry
