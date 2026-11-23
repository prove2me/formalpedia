-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_isInt_orbZ_inv
-- name    : Formalism.FourierDecayAlt.P.A5x4.isInt_orbZ_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:26:39.768441+00:00
-- url     : https://prove2.me/theorems/40fb2e8b-0c2e-4325-86df-96fcec7a9692
-- title:
--   A5x4: is Int orb Z inv
-- statement:
--   The A5x4 construction uses the is Int orb Z inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L83-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L83-L94

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x4

theorem Formalism.FourierDecayAlt.P.A5x4.isInt_orbZ_inv {K : Type} [CommRing K] (R : Subring K) (w : Point K)
    (a : lowW K w.1 w.2) (ha : a ∈ intSub R (lowW K w.1 w.2))
    (b : upUniG K w.1.sum) (hb : b ∈ intSub R (upUniG K w.1.sum))
    (x : lowW K w.1 w.2) (y : upUniG K w.1.sum) :
    IsInt R (orbZ w (a * x, y * b)) ↔ IsInt R (orbZ w (x, y)) := by sorry
