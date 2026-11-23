-- Prove2me | Theorems.Thm_Formalism_ELL_PadicMultiplication_mulN_succ
-- name    : Formalism.ELL.PadicMultiplication.mulN_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:53.050516+00:00
-- url     : https://prove2.me/theorems/69e71528-9682-47af-a868-a5d377582559
-- title:
--   Padic Multiplication: mul N succ
-- statement:
--   The Padic Multiplication construction uses the mul N succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/PadicMult.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/PadicMult.lean#L25-L27

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
variable {R : Type*} [CommRing R]

theorem Formalism.ELL.PadicMultiplication.mulN_succ (F : FormalGroup R) (m : ℕ) :
    mulN F (m + 1) = MvPowerSeries.subst
      (![mulN F m, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries := by sorry
