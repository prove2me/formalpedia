-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_EntryMinorBounds_entry_le_mx
-- name    : Formalism.FourierDecayAlt.P.EntryMinorBounds.entry_le_mx
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:32:49.816626+00:00
-- url     : https://prove2.me/theorems/762f0ee9-a55d-4476-9306-2b0a8d310419
-- title:
--   Entry Minor Bounds: entry le mx
-- statement:
--   The Entry Minor Bounds construction uses the entry le mx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryMinorBounds.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryMinorBounds.lean#L44-L47

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

theorem Formalism.FourierDecayAlt.P.EntryMinorBounds.entry_le_mx {α β : Type*} [Fintype α] [Fintype β] (M : Matrix α β ℂ) (i : α) (j : β) :
    ‖M i j‖ ≤ C2.mx M := by sorry
