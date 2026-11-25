-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_EHc_psi
-- name    : Formalism.FourierDecayAlt.P.JFxE.EHc_psi
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:36:11.234334+00:00
-- url     : https://prove2.me/theorems/56f08681-463a-4f65-bd95-d6deb46e5295
-- title:
--   JFx E: EHc psi
-- statement:
--   The JFx E construction uses the EHc psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EHcChange.lean#L61-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EHcChange.lean#L61-L75

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EHcChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.JFxE.EHc_psi {y : Mat k r} (hy : y ∈ GV k r) {φ F : Mat k r → E} {F' : Mat k r →L[ℝ] E} {U : Set (Mat k r)}
    {g : Mat k r} (hU : IsOpen U) (hgU : g ∈ U) (hg : g ∈ GV k r) (hF : HasFDerivAt F F' g)
    (hff : ∀ h ∈ U, h ∈ GV k r → φ h = F h) (c d : Fin (2 * r + k + 1)) :
    EHc k r y c d φ g = Psi F' g (y⁻¹ * Matrix.single c d 1 * y) := by sorry
