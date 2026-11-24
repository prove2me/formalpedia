-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_EntryMinorBounds_mx_le
-- name    : Formalism.FourierDecayAlt.P.EntryMinorBounds.mx_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:13:37.849525+00:00
-- url     : https://prove2.me/theorems/6d76eac9-3d3e-4df7-a540-70971fe2c1d9
-- title:
--   Entry Minor Bounds: mx le
-- statement:
--   The Entry Minor Bounds construction uses the mx le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryMinorBounds.lean#L49-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryMinorBounds.lean#L49-L56

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryMinorBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.EntryMinorBounds

theorem Formalism.FourierDecayAlt.P.EntryMinorBounds.mx_le {α β : Type*} [Fintype α] [Fintype β] (M : Matrix α β ℂ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i j, ‖M i j‖ ≤ c) : C2.mx M ≤ c := by sorry
