-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ubl_sub
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_sub
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:55:35.533723+00:00
-- url     : https://prove2.me/theorems/3fcfcf63-fd4b-4721-9d1e-f24b5d6224ac
-- title:
--   Admissible Lie Words: ubl sub
-- statement:
--   The Admissible Lie Words construction uses the ubl sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZinvBound.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZinvBound.lean#L48-L51

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZinvBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_sub {f : Mat k r → E} {S S' : Set (Mat k r)} (hS : S' ⊆ S) {n e γ : ℕ} (h : UBL f S n e γ) :
    UBL f S' n e γ := by sorry
