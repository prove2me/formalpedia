-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ub_app
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.ub_app
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:03:10.493873+00:00
-- url     : https://prove2.me/theorems/f2dabdb2-57b4-408c-a8b2-e17c09117d58
-- title:
--   Admissible Lie Words: ub app
-- statement:
--   The Admissible Lie Words construction uses the ub app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleWordLengthLe.lean#L168-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleWordLengthLe.lean#L168-L204

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Sq2UnitOfEqOneOfSq2EqDiv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
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
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.ub_app {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {a : Mat k r → (F →L[ℂ] E)} {b : Mat k r → F}
    (hla : LSS a S) (hlb : LSS b S) {n : ℕ} {Ca Cb : ℝ} {ea eb γ : ℕ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (ha : UB a S n Ca ea γ) (hb : UB b S n Cb eb γ) :
    UB (fun g => a g (b g)) S n (2 ^ n * (Ca * Cb)) (ea + eb) γ := by sorry
