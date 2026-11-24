-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_zinv_bound
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.zinv_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:26:18.814866+00:00
-- url     : https://prove2.me/theorems/2e71ceac-d30f-4c48-ad02-e6feb1171f12
-- title:
--   Admissible Lie Words: zinv bound
-- statement:
--   The Admissible Lie Words construction uses the zinv bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZinvBound.lean#L139-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZinvBound.lean#L139-L172

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

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.zinv_bound {c : ℝ} (hc : 0 < c) (m j : ℕ) :
    ∃ B : ℝ, ∀ z ∈ {z : ℂ | c ≤ Complex.normSq z}, ‖iteratedFDeriv ℝ j (zinv c m) z‖ ≤ B := by sorry
