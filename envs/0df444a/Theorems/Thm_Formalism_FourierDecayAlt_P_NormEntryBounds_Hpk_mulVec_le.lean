-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NormEntryBounds_Hpk_mulVec_le
-- name    : Formalism.FourierDecayAlt.P.NormEntryBounds.Hpk_mulVec_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:55:42.87853+00:00
-- url     : https://prove2.me/theorems/afef2487-da33-417d-bcbf-f6f25fbd757f
-- title:
--   Norm Entry Bounds: Hpk mul Vec le
-- statement:
--   The Norm Entry Bounds construction uses the Hpk mul Vec le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormEntryBounds.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormEntryBounds.lean#L28-L34

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryMinorBounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZhatSectionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormEntryBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2 C2x5 HermitianXiVector UnipotentSums EntryMinorBounds
open Formalism.FourierDecayAlt.P.NormEntryBounds
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.NormEntryBounds.Hpk_mulVec_le (y : Fin (2 * r + k + 1) → ℂ) (X : ℝ) (hy : ∀ p, ‖y p‖ ≤ X) (j : Fin (2 * r + k + 1)) :
    ‖(Hpk k r *ᵥ y) j‖ ≤ X := by sorry
