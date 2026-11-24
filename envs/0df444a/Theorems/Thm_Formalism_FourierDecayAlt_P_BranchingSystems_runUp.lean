-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_runUp
-- name    : Formalism.FourierDecayAlt.P.BranchingSystems.runUp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:52:12.495597+00:00
-- url     : https://prove2.me/theorems/96f48619-af85-49c6-9b3a-f72b2bddc72d
-- title:
--   Branching Systems: run Up
-- statement:
--   The Branching Systems construction uses the run Up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L27-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L27-L36

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BranchingSystems
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BranchingSystems
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {n : ℕ} {L : Fin (n + 1) → ℤ} {P : (Fin n → ℤ) → Prop}

theorem Formalism.FourierDecayAlt.P.BranchingSystems.runUp (hR : ∀ M, P M → ∀ i, (∀ j, M i ≠ L j) → P (Function.update M i (M i + 1)))
    (M : Fin n → ℤ) (i : Fin n) (t0 : ℤ) (h0 : P (Function.update M i t0)) (t : ℤ) (ht : t0 ≤ t) :
    (∀ t', t0 ≤ t' → t' < t → ∀ j, t' ≠ L j) → P (Function.update M i t) := by sorry
