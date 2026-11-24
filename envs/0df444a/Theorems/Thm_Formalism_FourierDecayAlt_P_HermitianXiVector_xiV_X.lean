-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_xiV_X
-- name    : Formalism.FourierDecayAlt.P.HermitianXiVector.xiV_X
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:44:23.264799+00:00
-- url     : https://prove2.me/theorems/85f1a9a3-40fe-4974-864b-6701dce62e4f
-- title:
--   Hermitian Xi Vector: xi V X
-- statement:
--   The Hermitian Xi Vector construction uses the xi V X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L65-L70

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

theorem Formalism.FourierDecayAlt.P.HermitianXiVector.xiV_X (ξ : Fin r → ℂ) : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → C2.xiV k r ξ i = 0 := by sorry
