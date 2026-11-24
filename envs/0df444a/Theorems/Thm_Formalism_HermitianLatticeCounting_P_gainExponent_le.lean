-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gainExponent_le
-- name    : Formalism.HermitianLatticeCounting.P.gainExponent_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:01.144118+00:00
-- url     : https://prove2.me/theorems/b21515d5-7e90-40c9-a296-bf8f4caabf26
-- title:
--   P: gain Exponent le
-- statement:
--   The P construction uses the gain Exponent le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeSumBounds.lean#L564-L570
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeSumBounds.lean#L564-L570

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.gainExponent_le (k r : ℕ) (hk : 1 ≤ k) : expo k r ≤ 2 * r := by sorry
