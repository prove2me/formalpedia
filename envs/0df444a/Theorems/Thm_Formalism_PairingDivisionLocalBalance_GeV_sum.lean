-- Prove2me | Theorems.Thm_Formalism_PairingDivisionLocalBalance_GeV_sum
-- name    : Formalism.PairingDivisionLocalBalance.GeV.sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:13.16702+00:00
-- url     : https://prove2.me/theorems/fe4fe095-e296-44a3-b3b2-795f003fb0d2
-- title:
--   Ge V: sum
-- statement:
--   The Ge V construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/PairingDivisorProofs/ValAdd.lean#L111-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/PairingDivisorProofs/ValAdd.lean#L111-L113

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

theorem Formalism.PairingDivisionLocalBalance.GeV.sum {w : Pl K} {c : ℝ} {ι : Type} (s : Finset ι) (f : ι → K)
    (h : ∀ i ∈ s, GeV w c (f i)) : GeV w c (∑ i ∈ s, f i) := by sorry
