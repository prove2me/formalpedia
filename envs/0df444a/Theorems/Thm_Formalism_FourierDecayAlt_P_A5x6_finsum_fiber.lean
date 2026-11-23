-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_finsum_fiber
-- name    : Formalism.FourierDecayAlt.P.A5x6.finsum_fiber
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:11.631988+00:00
-- url     : https://prove2.me/theorems/75990225-3464-42be-a58e-45506e6c0578
-- title:
--   A5x6: finsum fiber
-- statement:
--   The A5x6 construction uses the finsum fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelPropertiesOfHypotheses.lean#L292-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelPropertiesOfHypotheses.lean#L292-L324

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

theorem Formalism.FourierDecayAlt.P.A5x6.finsum_fiber {X Y T : Type} [AddGroup Y] [Fintype T] (κ : X → Y)
    (hκ : Function.Bijective κ) (g : T → Y) (f : T → ℂ) [∀ τ x, Decidable (g τ = -κ x)] :
    (Function.support fun x => ∑ τ : T, if g τ = -κ x then f τ else 0).Finite ∧
      ∑ᶠ x, ∑ τ : T, (if g τ = -κ x then f τ else 0) = ∑ τ : T, f τ := by sorry
