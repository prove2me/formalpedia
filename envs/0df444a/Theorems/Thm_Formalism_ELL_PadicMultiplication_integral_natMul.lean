-- Prove2me | Theorems.Thm_Formalism_ELL_PadicMultiplication_integral_natMul
-- name    : Formalism.ELL.PadicMultiplication.integral_natMul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:34.95506+00:00
-- url     : https://prove2.me/theorems/3b2b6de5-96fd-4451-bc4b-af54a14aa69d
-- title:
--   Padic Multiplication: integral nat Mul
-- statement:
--   The Padic Multiplication construction uses the integral nat Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/PadicMult.lean#L100-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/PadicMult.lean#L100-L103

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_PadicMult
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.ELL Formalism.ELL.PadicMultiplication
open Formalism.G Formalism.G.LogP
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.ELL.PadicMultiplication.integral_natMul (F : FormalGroup (unitBall K)) (m n : ℕ) :
    ‖coeff n ((mulN F m).map (unitBall K).subtype)‖ ≤ 1 := by sorry
