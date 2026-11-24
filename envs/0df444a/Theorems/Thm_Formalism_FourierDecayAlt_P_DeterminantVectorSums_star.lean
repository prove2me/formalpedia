-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DeterminantVectorSums_star
-- name    : Formalism.FourierDecayAlt.P.DeterminantVectorSums.star
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:32:23.521556+00:00
-- url     : https://prove2.me/theorems/5b88a45a-68d2-464e-bd94-d3b3a3e72b4b
-- title:
--   Determinant Vector Sums: star
-- statement:
--   The Determinant Vector Sums construction uses the star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StarSumLemmas.lean#L55-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StarSumLemmas.lean#L55-L66

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

theorem Formalism.FourierDecayAlt.P.DeterminantVectorSums.star (hE : GlRel E) (y : Fin (N + 1) → A) (hy : IsVec E y) (w : ℂ) (j : Fin (N + 1)) :
    ∑ l, Tch E (w - 1) j l * ((w + 1) • y l + ∑ c, E c l * y c) = y j * qdet E w := by sorry
