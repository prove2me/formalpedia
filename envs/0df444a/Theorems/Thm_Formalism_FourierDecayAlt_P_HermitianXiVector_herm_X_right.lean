-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_herm_X_right
-- name    : Formalism.FourierDecayAlt.P.HermitianXiVector.herm_X_right
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:44:17.635917+00:00
-- url     : https://prove2.me/theorems/632d199e-38ed-4ff8-ac9d-5fef58e21e71
-- title:
--   Hermitian Xi Vector: herm X right
-- statement:
--   The Hermitian Xi Vector construction uses the herm X right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L50-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L50-L63

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

theorem Formalism.FourierDecayAlt.P.HermitianXiVector.herm_X_right (v u : Fin (2 * r + k + 1) → ℂ) (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → v i = 0)
    (hu : ∀ i : Fin (2 * r + k + 1), r + k < i.val → u i = 0) : herm (Hpk k r) u v = 0 := by sorry
