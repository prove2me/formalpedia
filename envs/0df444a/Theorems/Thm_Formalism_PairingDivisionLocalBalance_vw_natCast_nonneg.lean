-- Prove2me | Theorems.Thm_Formalism_PairingDivisionLocalBalance_vw_natCast_nonneg
-- name    : Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:02.660524+00:00
-- url     : https://prove2.me/theorems/65fd7abc-a89d-41a2-b1ab-4f4a85d96742
-- title:
--   Pairing Division Local Balance: vw nat Cast nonneg
-- statement:
--   The Pairing Division Local Balance construction uses the vw nat Cast nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/PairingDivisorProofs/Height.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/PairingDivisorProofs/Height.lean#L13-L16

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

theorem Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg {K : Type} [Field K] [NumberField K] [StarRing K] (w : Pl K) (n : ℕ) :
    0 ≤ vw w (n : K) := by sorry
