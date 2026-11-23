-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_blkM_isInt
-- name    : Formalism.FourierDecayAlt.P.A5x8.blkM_isInt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:11:50.480852+00:00
-- url     : https://prove2.me/theorems/b13103e4-6af5-4a5f-b0b2-26ec6b023716
-- title:
--   A5x8: blk M is Int
-- statement:
--   The A5x8 construction uses the blk M is Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L91-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L91-L103

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] {m N : ℕ}

theorem Formalism.FourierDecayAlt.P.A5x8.blkM_isInt (R : Subring K) (hN : N = m + 1) (A : Matrix (Fin m) (Fin m) K)
    (b a : Fin m → K) (d : K) : IsInt R (blkM hN A b a d) ↔
      IsInt R A ∧ (∀ i, b i ∈ R) ∧ (∀ j, a j ∈ R) ∧ d ∈ R := by sorry
