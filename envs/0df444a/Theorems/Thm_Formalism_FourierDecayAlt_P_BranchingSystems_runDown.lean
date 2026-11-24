-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_runDown
-- name    : Formalism.FourierDecayAlt.P.BranchingSystems.runDown
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:52:39.545683+00:00
-- url     : https://prove2.me/theorems/3c9d8953-aefc-4474-8c45-9f4aded4f52a
-- title:
--   Branching Systems: run Down
-- statement:
--   The Branching Systems construction uses the run Down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L38-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L38-L47

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

theorem Formalism.FourierDecayAlt.P.BranchingSystems.runDown (hD : ∀ M, P M → ∀ i, (∀ j, M i - 1 ≠ L j) → P (Function.update M i (M i - 1)))
    (M : Fin n → ℤ) (i : Fin n) (t0 : ℤ) (h0 : P (Function.update M i t0)) (t : ℤ) (ht : t ≤ t0) :
    (∀ t', t ≤ t' → t' < t0 → ∀ j, t' ≠ L j) → P (Function.update M i t) := by sorry
