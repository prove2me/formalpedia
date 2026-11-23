-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_phase_one
-- name    : Formalism.FourierDecayAlt.P.A5x7.phase_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:26:57.155463+00:00
-- url     : https://prove2.me/theorems/6a38cff4-ff73-4009-99a4-e248d341eeb9
-- title:
--   A5x7: phase one
-- statement:
--   The A5x7 construction uses the phase one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AddedBlockKernelSupport.lean#L470-L488
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AddedBlockKernelSupport.lean#L470-L488

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x7
variable {K : Type} [CommRing K] (R : Subring K)

theorem Formalism.FourierDecayAlt.P.A5x7.phase_one (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (w : Point K)
    (p : lowW K w.1 w.2 × upUniG K w.1.sum)
    (h1 : p.1 ∈ intSub R (lowW K w.1 w.2)) (h2 : p.2 ∈ intSub R (upUniG K w.1.sum)) :
    phase ψ p = 1 := by sorry
