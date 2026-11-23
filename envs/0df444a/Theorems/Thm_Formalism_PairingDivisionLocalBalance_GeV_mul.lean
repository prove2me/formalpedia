-- Prove2me | Theorems.Thm_Formalism_PairingDivisionLocalBalance_GeV_mul
-- name    : Formalism.PairingDivisionLocalBalance.GeV.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:56.117799+00:00
-- url     : https://prove2.me/theorems/08e3a2f7-9084-41da-b9e0-1593b67dca94
-- title:
--   Ge V: mul
-- statement:
--   The Ge V construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/PairingDivisorProofs/ValAdd.lean#L115-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/PairingDivisorProofs/ValAdd.lean#L115-L129

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_ValAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)
open Formalism Formalism.PairingDivisionLocalBalance
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.PairingDivisionLocalBalance.GeV.mul {w : Pl K} {c c' : ℝ} {x y : K} (hx : GeV w c x) (hy : GeV w c' y) :
    GeV w (c + c') (x * y) := by sorry
