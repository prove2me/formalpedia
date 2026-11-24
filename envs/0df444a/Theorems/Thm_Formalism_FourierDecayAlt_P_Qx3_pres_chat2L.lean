-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_pres_chat2L
-- name    : Formalism.FourierDecayAlt.P.Qx3.pres_chat2L
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:19:50.168065+00:00
-- url     : https://prove2.me/theorems/8f7bdf9d-9c31-4d6d-949e-5d9d137cb45b
-- title:
--   Qx3: pres chat2 L
-- statement:
--   The Qx3 construction uses the pres chat2 L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeylCellConjTransposeMulApply.lean#L331-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeylCellConjTransposeMulApply.lean#L331-L343

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {i : Fin (r + 1)} {U₀ : Set (XX k r)}

theorem Formalism.FourierDecayAlt.P.Qx3.pres_chat2L (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ)
    (ha : ∀ j, SmoothFam k r i U₀ (fun _ g => a g j)) (ha' : ∀ j, SmoothFam k r i U₀ (fun _ g => a' g j))
    (hβ : ∀ j, SmoothFam k r i U₀ (fun _ g => β g j)) (hβ' : ∀ j, SmoothFam k r i U₀ (fun _ g => β' g j)) :
    Pres (E := E) i U₀ (chat2L (EH k r) (posL k r i) u a a' β β') := by sorry
