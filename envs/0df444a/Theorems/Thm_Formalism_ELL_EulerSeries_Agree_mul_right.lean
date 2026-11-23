-- Prove2me | Theorems.Thm_Formalism_ELL_EulerSeries_Agree_mul_right
-- name    : Formalism.ELL.EulerSeries.Agree.mul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:31.040848+00:00
-- url     : https://prove2.me/theorems/22c00c76-8365-47fb-a199-6030d8d0eec1
-- title:
--   Agree: mul right
-- statement:
--   The Agree construction uses the mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ConstantCoeffLogOnePlus.lean#L60-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ConstantCoeffLogOnePlus.lean#L60-L68

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ConstantCoeffLogOnePlus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.EulerSeries
open Formalism.G Formalism.ELL
variable {K : Type*} [NormedField K] [CharZero K] {σ : Type} [DecidableEq σ]

theorem Formalism.ELL.EulerSeries.Agree.mul_right {N : ℕ} {F G : MvPowerSeries σ K} (h : Agree N F G)
    (H : MvPowerSeries σ K) : Agree N (F * H) (G * H) := by sorry
