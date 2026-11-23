-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_sum_eq_zero_of_shift
-- name    : Formalism.FourierDecayAlt.P.A5x9.sum_eq_zero_of_shift
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:46:27.730032+00:00
-- url     : https://prove2.me/theorems/c789903e-fafc-4e20-aff1-68e6e8309e1a
-- title:
--   A5x9: sum eq zero of shift
-- statement:
--   The A5x9 construction uses the sum eq zero of shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L223-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L223-L241

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9

theorem Formalism.FourierDecayAlt.P.A5x9.sum_eq_zero_of_shift {α : Type} (E : Finset α) (Φ : α → ℂ) (S : α → α)
    (hS : Function.Injective S) (hE : ∀ q ∈ E, S q ∈ E) (ζ : ℂ) (hζ : ζ ≠ 1)
    (hΦ : ∀ q ∈ E, Φ (S q) = ζ * Φ q) : ∑ q ∈ E, Φ q = 0 := by sorry
