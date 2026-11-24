-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_SAdd_shear_alg
-- name    : Formalism.L2.Th1.B.SAdd.shear_alg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:02:01.654747+00:00
-- url     : https://prove2.me/theorems/9bc96422-da4c-45c4-a941-85578fda9007
-- title:
--   SAdd: shear alg
-- statement:
--   The SAdd construction uses the shear alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/ConstantCoeffQuotientXSq.lean#L138-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/ConstantCoeffQuotientXSq.lean#L138-L145

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffQuotientXSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.SAdd
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.B.SAdd.shear_alg {R : Type} [CommRing R] (k a x y x1 y1 : R)
    (hx : x1 ^ 2 = 1 + a * x ^ 2 + k * (x ^ 2) ^ 2)
    (hy : y1 ^ 2 = 1 + a * y ^ 2 + k * (y ^ 2) ^ 2) :
    (1 - k * x ^ 2 * y ^ 2) *
        (y * ((a + 2 * k * x ^ 2) * x) - x * ((a + 2 * k * y ^ 2) * y)) =
      (x * y1 + y * x1) *
        (-(k * (2 * x * x1) * y ^ 2) + k * x ^ 2 * (2 * y * y1)) := by sorry
