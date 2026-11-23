-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_isoZZ_refl
-- name    : Formalism.FourierDecayAlt.P.A5x4.isoZZ_refl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:10:07.652667+00:00
-- url     : https://prove2.me/theorems/b2de0a8b-eec1-4f99-b171-c6072c83b21a
-- title:
--   A5x4: iso ZZ refl
-- statement:
--   The A5x4 construction uses the iso ZZ refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L357-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L357-L359

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
variable {K : Type} [CommRing K] (R : Subring K)

theorem Formalism.FourierDecayAlt.P.A5x4.isoZZ_refl {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) :
    LinearEquiv.refl R (coker R Z) ∈ isoZZ R Z Z := by sorry
