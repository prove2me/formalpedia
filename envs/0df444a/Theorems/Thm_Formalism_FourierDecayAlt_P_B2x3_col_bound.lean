-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_col_bound
-- name    : Formalism.FourierDecayAlt.P.B2x3.col_bound
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:54:42.069713+00:00
-- url     : https://prove2.me/theorems/0b6ec319-e143-408b-8a1d-05f4ad62aaf9
-- title:
--   B2x3: col bound
-- statement:
--   The B2x3 construction uses the col bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L734-L769
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L734-L769

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x3.col_bound (z : Fin (k + 1) → ℂ) (hT : (star z ⬝ᵥ (Hb k *ᵥ z)).re < 0) :
    ∃ R : ℝ, ∀ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, μᴴ * Hb k * μ = Hb k → μ *ᵥ z = z → ∀ i j, ‖μ i j‖ ≤ R := by sorry
