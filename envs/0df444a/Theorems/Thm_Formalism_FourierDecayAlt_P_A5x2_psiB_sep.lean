-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_psiB_sep
-- name    : Formalism.FourierDecayAlt.P.A5x2.psiB_sep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:36.181964+00:00
-- url     : https://prove2.me/theorems/926af338-897c-4b91-a72d-afd2829a5e67
-- title:
--   A5x2: psi B sep
-- statement:
--   The A5x2 construction uses the psi B sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L93-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L93-L106

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x2
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ)

theorem Formalism.FourierDecayAlt.P.A5x2.psiB_sep (hsd : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) (hψ : ∀ r ∈ R, ψ r = 1)
    (x : KR R) (hx : ∀ r : R, psiB R ψ hψ (r • x) = 1) : x = 0 := by sorry
