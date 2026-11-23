-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_psd_comap
-- name    : Formalism.FourierDecayAlt.P.A5x6.psd_comap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:25.270711+00:00
-- url     : https://prove2.me/theorems/c9f33db2-b13e-447e-98b2-3b8be1ba8302
-- title:
--   A5x6: psd comap
-- statement:
--   The A5x6 construction uses the psd comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelPropertiesOfHypotheses.lean#L559-L588
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelPropertiesOfHypotheses.lean#L559-L588

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x6

theorem Formalism.FourierDecayAlt.P.A5x6.psd_comap {X Y : Type} [DecidableEq Y] (k : Y → Y → ℂ) (f : X → Y) (F : Finset X)
    (h : IsPSD (F.image f) k) : IsPSD F (fun x y => k (f x) (f y)) := by sorry
