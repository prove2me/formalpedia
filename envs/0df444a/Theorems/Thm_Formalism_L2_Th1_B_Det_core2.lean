-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Det_core2
-- name    : Formalism.L2.Th1.B.Det.core2
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:59:58.270246+00:00
-- url     : https://prove2.me/theorems/e469f754-9d09-4c74-a8a3-61d41bb2cc8f
-- title:
--   Det: core2
-- statement:
--   The Det construction uses the core2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L222-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L222-L249

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Det
open Formalism.InvariantFactorPaths.G7 (at1)

theorem Formalism.L2.Th1.B.Det.core2 {R : Type} [CommRing R] (a b c Xa Ya Xb Yb Xc Yc h g3 dXa dXb dXc dYb dYc : R)
    (Ca : Ya ^ 2 = 4 * Xa ^ 3 - 2 * h * a ^ 4 * Xa - g3 * a ^ 6)
    (Cb : Yb ^ 2 = 4 * Xb ^ 3 - 2 * h * b ^ 4 * Xb - g3 * b ^ 6)
    (Cc : Yc ^ 2 = 4 * Xc ^ 3 - 2 * h * c ^ 4 * Xc - g3 * c ^ 6)
    (ha : a * dXa = Ya + 2 * Xa) (hb : b * dXb = Yb + 2 * Xb) (hc : c * dXc = Yc + 2 * Xc)
    (kb : b * dYb = 6 * Xb ^ 2 - h * b ^ 4 + 3 * Yb)
    (kc : c * dYc = 6 * Xc ^ 2 - h * c ^ 4 + 3 * Yc) :
    (a * b * c) * (2 * (a ^ 2 * Xb - b ^ 2 * Xa) * (a ^ 2 * Xc - c ^ 2 * Xa) *
        (b ^ 2 * Xc - c ^ 2 * Xb) *
      ((a ^ 3 * ((Xb + b * dXb) * Yc - dYb * (c * Xc)) -
          a * Xa * (3 * b ^ 2 * Yc - dYb * c ^ 3) +
          Ya * (3 * b ^ 2 * (c * Xc) - (Xb + b * dXb) * c ^ 3)) -
        (a ^ 3 * (b * Xb * dYc - Yb * (Xc + c * dXc)) -
          a * Xa * (b ^ 3 * dYc - Yb * (3 * c ^ 2)) +
          Ya * (b ^ 3 * (Xc + c * dXc) - b * Xb * (3 * c ^ 2))))) =
    (a * b * c) * ((a ^ 3 * (b * Xb * Yc - Yb * (c * Xc)) - a * Xa * (b ^ 3 * Yc - Yb * c ^ 3) +
        Ya * (b ^ 3 * (c * Xc) - b * Xb * c ^ 3)) *
      (-((2 * a * Xb - b ^ 2 * dXa) - (a ^ 2 * dXb - 2 * b * Xa)) *
          (a ^ 2 * Xc - c ^ 2 * Xa) * (b ^ 2 * Xc - c ^ 2 * Xb) +
        ((2 * a * Xc - c ^ 2 * dXa) - (a ^ 2 * dXc - 2 * c * Xa)) *
          (a ^ 2 * Xb - b ^ 2 * Xa) * (b ^ 2 * Xc - c ^ 2 * Xb) +
        2 * ((2 * b * Xc - c ^ 2 * dXb) - (b ^ 2 * dXc - 2 * c * Xb)) *
          (a ^ 2 * Xb - b ^ 2 * Xa) * (a ^ 2 * Xc - c ^ 2 * Xa))) := by sorry
