-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ubl_app
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_app
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:26:24.21347+00:00
-- url     : https://prove2.me/theorems/2b60fe46-6760-44c0-a5d7-0624811c9cc4
-- title:
--   Admissible Lie Words: ubl app
-- statement:
--   The Admissible Lie Words construction uses the ubl app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZinvBound.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZinvBound.lean#L36-L41

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

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_app {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {a : Mat k r → (F →L[ℂ] E)} {b : Mat k r → F} {n ea eb γ : ℕ} (ha : UBL a S n ea γ) (hb : UBL b S n eb γ) :
    UBL (fun g => a g (b g)) S n (ea + eb) γ := by sorry
