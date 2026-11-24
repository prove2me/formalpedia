-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_kernel_quotient_finite
-- name    : Formalism.FourierDecayAlt.P.kernel_quotient_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:56:59.251811+00:00
-- url     : https://prove2.me/theorems/bdbb7920-85ec-40b3-a402-23f6bd20f54e
-- title:
--   P: kernel quotient finite
-- statement:
--   The P construction uses the kernel quotient finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L130-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L130-L140

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x4

theorem Formalism.FourierDecayAlt.P.kernel_quotient_finite : Formalism.FourierDecayAlt.A5.KpFinite := by sorry
