-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ubl_prod
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_prod
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:25:09.730701+00:00
-- url     : https://prove2.me/theorems/c7b545d5-9854-409c-afef-609c3927cbc5
-- title:
--   Admissible Lie Words: ubl prod
-- statement:
--   The Admissible Lie Words construction uses the ubl prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZinvBound.lean#L63-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZinvBound.lean#L63-L73

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

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_prod {ι : Type*} [DecidableEq ι] {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {n γ : ℕ} (s : Finset ι)
    (f : ι → Mat k r → ℂ) (h : ∀ i ∈ s, UBL (f i) S n 0 γ) : UBL (fun g => ∏ i ∈ s, f i g) S n 0 γ := by sorry
