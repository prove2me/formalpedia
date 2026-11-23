-- Prove2me | Theorems.Thm_Formalism_PairingDivisionLocalBalance_vw_pow
-- name    : Formalism.PairingDivisionLocalBalance.vw_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:24.304179+00:00
-- url     : https://prove2.me/theorems/303debb0-f3dc-41d2-9079-00319ff1a7e2
-- title:
--   Pairing Division Local Balance: vw pow
-- statement:
--   The Pairing Division Local Balance construction uses the vw pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/PairingDivisorProofs/Height.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/PairingDivisorProofs/Height.lean#L44-L49

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_SumValuationNat
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
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

theorem Formalism.PairingDivisionLocalBalance.vw_pow {K : Type} [Field K] [NumberField K] [StarRing K] (w : Pl K) (a : K) (ha : a ≠ 0) (n : ℕ) :
    vw w (a ^ n) = n * vw w a := by sorry
