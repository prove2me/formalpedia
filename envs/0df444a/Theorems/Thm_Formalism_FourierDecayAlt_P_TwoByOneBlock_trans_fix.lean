-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans_fix
-- name    : Formalism.FourierDecayAlt.P.TwoByOneBlock.trans_fix
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:24:05.799471+00:00
-- url     : https://prove2.me/theorems/716b489f-df64-4e93-b2d2-e5d7a8be6d22
-- title:
--   Two By One Block: trans fix
-- statement:
--   The Two By One Block construction uses the trans fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L676-L707
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L676-L707

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem Formalism.FourierDecayAlt.P.TwoByOneBlock.trans_fix {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (hH : Hᴴ = H) (z v₁ v₂ : Fin m → ℂ) (T : ℝ) (hT : T ≠ 0)
    (hz : herm H z z = -(T : ℂ)) (h12 : herm H v₁ v₁ = herm H v₂ v₂) (hζ : herm H v₁ z = herm H v₂ z)
    (hne : (herm H v₁ v₁).re * T + Complex.normSq (herm H v₁ z) ≠ 0) :
    ∃ g ∈ UH H, g *ᵥ z = z ∧ g *ᵥ v₁ = v₂ := by sorry
