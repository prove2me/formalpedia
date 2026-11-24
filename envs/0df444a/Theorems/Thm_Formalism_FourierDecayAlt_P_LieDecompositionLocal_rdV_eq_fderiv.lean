-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_eq_fderiv
-- name    : Formalism.FourierDecayAlt.P.LieDecompositionLocal.rdV_eq_fderiv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:48:18.811888+00:00
-- url     : https://prove2.me/theorems/81a16b83-1e75-409c-8ca7-028e7f8e3dd4
-- title:
--   Lie Decomposition Local: rd V eq fderiv
-- statement:
--   The Lie Decomposition Local construction uses the rd V eq fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieDecompositionLocal.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieDecompositionLocal.lean#L17-L25

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LieDecompositionLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.LieDecompositionLocal.rdV_eq_fderiv {Φ Φ' : Mat k r → E} {U : Set (Mat k r)} {m : ℕ∞} (hm : 1 ≤ m) (hU : IsOpen U)
    {g X : Mat k r} (hgU : g ∈ U) (hgG : g ∈ GV k r) (hc : ContDiffOn ℝ (m : WithTop ℕ∞) Φ' U)
    (he : ∀ x ∈ U, x ∈ GV k r → Φ x = Φ' x) (hX : inLie k r X) :
    RdV X Φ g = fderiv ℝ Φ' g (g * X) := by sorry
