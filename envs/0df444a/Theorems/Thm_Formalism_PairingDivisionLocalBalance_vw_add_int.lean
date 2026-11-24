-- Prove2me | Theorems.Thm_Formalism_PairingDivisionLocalBalance_vw_add_int
-- name    : Formalism.PairingDivisionLocalBalance.vw_add_int
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:18:17.150958+00:00
-- url     : https://prove2.me/theorems/806ee104-d042-4f9a-a2ad-4ee09c200276
-- title:
--   Pairing Division Local Balance: vw add int
-- statement:
--   The Pairing Division Local Balance construction uses the vw add int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/PairingDivisorProofs/ValAdd.lean#L35-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/PairingDivisorProofs/ValAdd.lean#L35-L44

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

theorem Formalism.PairingDivisionLocalBalance.vw_add_int (w : Pl K) (x y : 𝓞 K) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (vw w (x : K)) (vw w (y : K)) ≤ vw w ((x + y : 𝓞 K) : K) := by sorry
