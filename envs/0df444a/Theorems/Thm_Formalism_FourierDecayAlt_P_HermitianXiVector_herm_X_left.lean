-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_herm_X_left
-- name    : Formalism.FourierDecayAlt.P.HermitianXiVector.herm_X_left
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:44:23.860797+00:00
-- url     : https://prove2.me/theorems/4ae5ac91-4a8a-4d53-a130-6af7c8fc0350
-- title:
--   Hermitian Xi Vector: herm X left
-- statement:
--   The Hermitian Xi Vector construction uses the herm X left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L35-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L35-L48

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianXiVector
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
open Formalism.FourierDecayAlt.P.HermitianXiVector
open C2x5 FlagSpanVanishing
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.HermitianXiVector.herm_X_left (v u : Fin (2 * r + k + 1) → ℂ) (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → v i = 0)
    (hu : ∀ i : Fin (2 * r + k + 1), r + k < i.val → u i = 0) : herm (Hpk k r) v u = 0 := by sorry
