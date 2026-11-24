-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_nEich_apply
-- name    : Formalism.FourierDecayAlt.P.HermitianXiVector.nEich_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:44:57.787135+00:00
-- url     : https://prove2.me/theorems/86530488-4536-4dd2-9498-7cf60574b4dd
-- title:
--   Hermitian Xi Vector: n Eich apply
-- statement:
--   The Hermitian Xi Vector construction uses the n Eich apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L95-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L95-L101

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

theorem Formalism.FourierDecayAlt.P.HermitianXiVector.nEich_apply (z : Fin (2 * r + k + 1) → ℂ) (ξ : Fin r → ℂ) (y : Fin (2 * r + k + 1) → ℂ) :
    C2.nEich k r z ξ *ᵥ y = y + ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) • (-(herm (Hpk k r) y z) • C2.xiV k r ξ +
      herm (Hpk k r) y (C2.xiV k r ξ) • z + ((1 / 2 : ℂ) * herm (Hpk k r) y (C2.xiV k r ξ)) • C2.xiV k r ξ) := by sorry
