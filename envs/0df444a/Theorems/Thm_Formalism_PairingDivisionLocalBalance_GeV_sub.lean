-- Prove2me | Theorems.Thm_Formalism_PairingDivisionLocalBalance_GeV_sub
-- name    : Formalism.PairingDivisionLocalBalance.GeV.sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:10:16.155212+00:00
-- url     : https://prove2.me/theorems/418a015c-1fc6-4eba-b984-ec8f372df79a
-- title:
--   Ge V: sub
-- statement:
--   The Ge V construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/PairingDivisorProofs/ValAdd.lean#L168-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/PairingDivisorProofs/ValAdd.lean#L168-L170

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

theorem Formalism.PairingDivisionLocalBalance.GeV.sub {w : Pl K} {x y : K} (hx : GeV w 0 x) (hy : GeV w 0 y) : GeV w 0 (x - y) := by sorry
