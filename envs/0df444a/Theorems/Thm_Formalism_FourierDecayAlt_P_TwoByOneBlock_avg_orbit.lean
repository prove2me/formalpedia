-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_avg_orbit
-- name    : Formalism.FourierDecayAlt.P.TwoByOneBlock.avg_orbit
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:23:02.738145+00:00
-- url     : https://prove2.me/theorems/fb43ba36-7a5e-46d7-b0d9-8f10f489ef45
-- title:
--   Two By One Block: avg orbit
-- statement:
--   The Two By One Block construction uses the avg orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L1396-L1410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L1396-L1410

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
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.TwoByOneBlock.avg_orbit {z : Fin (2 * r + k + 1) → ℂ} {μW : Measure (Mt k r)}
    (hW : IsHaarOn (UWset k r z) μW) {F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F)
    {h₁ : Mat k r} (hh₁ : h₁ ∈ UWset k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    ∫⁻ h, F (act h v) ∂μW = ∫⁻ h, F (act h (h₁ *ᵥ v)) ∂μW := by sorry
