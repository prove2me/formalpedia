-- Prove2me | Theorems.Thm_Formalism_PairingDivisionLocalBalance_vw_add
-- name    : Formalism.PairingDivisionLocalBalance.vw_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:33.689932+00:00
-- url     : https://prove2.me/theorems/103656d8-0060-46ab-88f0-900c598093a0
-- title:
--   Pairing Division Local Balance: vw add
-- statement:
--   The Pairing Division Local Balance construction uses the vw add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/PairingDivisorProofs/ValAdd.lean#L65-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/PairingDivisorProofs/ValAdd.lean#L65-L89

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

theorem Formalism.PairingDivisionLocalBalance.vw_add (w : Pl K) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    min (vw w a) (vw w b) ≤ vw w (a + b) := by sorry
