-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NormEntryBounds_gN_le
-- name    : Formalism.FourierDecayAlt.P.NormEntryBounds.gN_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:54:40.346996+00:00
-- url     : https://prove2.me/theorems/baf90049-bd28-4142-b1e8-d658d6eeb25f
-- title:
--   Norm Entry Bounds: g N le
-- statement:
--   The Norm Entry Bounds construction uses the g N le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormEntryBounds.lean#L15-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormEntryBounds.lean#L15-L26

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

theorem Formalism.FourierDecayAlt.P.NormEntryBounds.gN_le (g : B.Mat k r) (E : ℝ) (hE : 0 ≤ E) (h : ∀ i j, ‖g i j‖ ≤ E) :
    B.gN g ≤ ((2 * r + k + 1 : ℕ) : ℝ) * E := by sorry
