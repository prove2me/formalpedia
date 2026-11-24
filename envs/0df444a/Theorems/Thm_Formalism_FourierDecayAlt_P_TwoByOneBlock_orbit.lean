-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_orbit
-- name    : Formalism.FourierDecayAlt.P.TwoByOneBlock.orbit
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:26:26.053534+00:00
-- url     : https://prove2.me/theorems/1a12c41d-2140-46b0-80e1-bcafcf1be0b8
-- title:
--   Two By One Block: orbit
-- statement:
--   The Two By One Block construction uses the orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L735-L749
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L735-L749

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

theorem Formalism.FourierDecayAlt.P.TwoByOneBlock.orbit {z v₁ v₂ : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hv₁ : inWb k r v₁) (hv₂ : inWb k r v₂)
    (hT : Tz k r z ≠ 0) (h12 : herm (Hpk k r) v₁ v₁ = herm (Hpk k r) v₂ v₂)
    (hζ : herm (Hpk k r) v₁ z = herm (Hpk k r) v₂ z)
    (hne : (herm (Hpk k r) v₁ v₁).re * Tz k r z + Complex.normSq (herm (Hpk k r) v₁ z) ≠ 0) :
    ∃ h ∈ UWset k r z, h *ᵥ v₁ = v₂ := by sorry
