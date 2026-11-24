-- Prove2me | Theorems.Thm_Formalism_PairingDivisionLocalBalance_GeV_int
-- name    : Formalism.PairingDivisionLocalBalance.GeV.int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:42.039788+00:00
-- url     : https://prove2.me/theorems/a80157b1-2b32-4538-98d6-fa965b81d3e9
-- title:
--   Ge V: int
-- statement:
--   The Ge V construction uses the int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/PairingDivisorProofs/ValAdd.lean#L141-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/PairingDivisorProofs/ValAdd.lean#L141-L152

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

theorem Formalism.PairingDivisionLocalBalance.GeV.int (w : Pl K) (x : 𝓞 K) : GeV w 0 (x : K) := by sorry
