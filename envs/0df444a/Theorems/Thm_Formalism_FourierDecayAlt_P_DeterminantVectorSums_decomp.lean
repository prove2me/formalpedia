-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DeterminantVectorSums_decomp
-- name    : Formalism.FourierDecayAlt.P.DeterminantVectorSums.decomp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:32:58.561056+00:00
-- url     : https://prove2.me/theorems/bcc61944-67be-4c49-9800-d5d7af2efbd2
-- title:
--   Determinant Vector Sums: decomp
-- statement:
--   The Determinant Vector Sums construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StarSumLemmas.lean#L175-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StarSumLemmas.lean#L175-L221

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
variable {W : Type} [AddCommGroup W] [Module ℂ W]

theorem Formalism.FourierDecayAlt.P.DeterminantVectorSums.decomp (hPV : PolyVanish) (G : Submodule ℂ W) (K : Module.End ℂ W) (hK : ∀ x ∈ G, K x ∈ G)
    (A : ℕ → Module.End ℂ W) (N : ℕ) (r : Fin (N + 1) → ℂ) (hr : Function.Injective r)
    (h : ∀ x ∈ G, ∀ u : ℂ, (∑ s ∈ range (N + 1), u ^ s • A s) (u • x - K x) = (∏ j, (u - r j)) • x) :
    ∀ x ∈ G, ∃ Φ : Fin (N + 1) → W, (∀ i, Φ i ∈ G) ∧ ∑ i, Φ i = x ∧
      ∀ i u, (∑ s ∈ range (N + 1), u ^ s • A s) (Φ i) = (∏ j ∈ univ.erase i, (u - r j)) • Φ i := by sorry
