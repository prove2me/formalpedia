-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DeterminantReindex_perm_of_range
-- name    : Formalism.FourierDecayAlt.P.DeterminantReindex.perm_of_range
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:12:40.573197+00:00
-- url     : https://prove2.me/theorems/a7bb2b6a-adc0-494e-b273-00a53d8dc145
-- title:
--   Determinant Reindex: perm of range
-- statement:
--   The Determinant Reindex construction uses the perm of range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DeterminantReindex.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DeterminantReindex.lean#L11-L17

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DeterminantReindex
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
open Formalism.FourierDecayAlt.P.DeterminantReindex
open C2x2 CardInsertEmbedding

theorem Formalism.FourierDecayAlt.P.DeterminantReindex.perm_of_range {m k : ℕ} (e ρ : Fin k → Fin m) (he : Function.Injective e)
    (hr : ∀ t, ∃ s, ρ s = e t) : ∃ τ : Equiv.Perm (Fin k), ∀ t, e t = ρ (τ t) := by sorry
