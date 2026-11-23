-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_inv_iso
-- name    : Formalism.FourierDecayAlt.P.A5x8.inv_iso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:46.308611+00:00
-- url     : https://prove2.me/theorems/f6c41b9a-ac88-4ee5-97f3-3da00e42aae7
-- title:
--   A5x8: inv iso
-- statement:
--   The A5x8 construction uses the inv iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L818-L840
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L818-L840

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
variable {K : Type} [CommRing K] (R : Subring K)

theorem Formalism.FourierDecayAlt.P.A5x8.inv_iso (w : Point K) (a : lowW K w.1 w.2) (ha : a ∈ intSub R (lowW K w.1 w.2))
    (b : upUniG K w.1.sum) (hb : b ∈ intSub R (upUniG K w.1.sum))
    (x : lowW K w.1 w.2) (y : upUniG K w.1.sum) :
    ∃ φ : coker R (orbZ w (x, y)) ≃ₗ[R] coker R (orbZ w (a * x, y * b)),
      φ ∈ isoZZ R (orbZ w (x, y)) (orbZ w (a * x, y * b)) := by sorry
