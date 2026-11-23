-- Prove2me | Theorems.Thm_Formalism_ELL_EulerSeries_eul_truncLog
-- name    : Formalism.ELL.EulerSeries.eul_truncLog
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:23.236293+00:00
-- url     : https://prove2.me/theorems/d38fbf18-f25b-47d5-a64f-99bf24ede157
-- title:
--   Euler Series: eul trunc Log
-- statement:
--   The Euler Series construction uses the eul trunc Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ConstantCoeffLogOnePlus.lean#L116-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ConstantCoeffLogOnePlus.lean#L116-L128

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

theorem Formalism.ELL.EulerSeries.eul_truncLog (f : MvPowerSeries σ K) (M : ℕ) :
    eulFun (truncLog (M + 1) f) = (∑ k ∈ Finset.range M, (-f) ^ k) * eulFun f := by sorry
