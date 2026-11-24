-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ubl_chi
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_chi
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:57:35.782781+00:00
-- url     : https://prove2.me/theorems/81066a3a-8943-4ad9-85f6-67cb23e4fdf0
-- title:
--   Admissible Lie Words: ubl chi
-- statement:
--   The Admissible Lie Words construction uses the ubl chi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutoffIteratedFDerivBounded.lean#L164-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutoffIteratedFDerivBounded.lean#L164-L193

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DminStarPd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutoffIteratedFDerivBounded
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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_chi (D : RealPlaceData k r Wp Wq) {χ₀ : ℝ → ℝ} (hχ : C6.IsCut0 χ₀) (de : ℝ) (L : Finset (Fin (r + 2)))
    (n : ℕ) : UBL (fun g => ((C6.chiAll D χ₀ de L g : ℝ) : ℂ)) (GV k r) n 0 (2 * r + 2) := by sorry
