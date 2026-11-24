-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DeterminantVectorSums_MM_apply
-- name    : Formalism.FourierDecayAlt.P.DeterminantVectorSums.MM_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:32:56.776577+00:00
-- url     : https://prove2.me/theorems/12386be6-721c-4a2f-b0e1-73c5523146f6
-- title:
--   Determinant Vector Sums: MM apply
-- statement:
--   The Determinant Vector Sums construction uses the MM apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StarSumLemmas.lean#L247-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StarSumLemmas.lean#L247-L249

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
variable {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V)

theorem Formalism.FourierDecayAlt.P.DeterminantVectorSums.MM_apply (T : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V) (x : Fin (N + 1) → V) (j : Fin (N + 1)) :
    MM T x j = ∑ l, T j l (x l) := by sorry
