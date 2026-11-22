-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_exists_coord_ne_zero
-- name    : Formalism.LogVandermondeBounds.product_first_zeroth_parts.exists_coord_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:00:36.255454+00:00
-- url     : https://prove2.me/theorems/0fb5277c-7650-4925-a4b3-49681d444808
-- title:
--   product first zeroth parts: exists coord ne zero
-- statement:
--   The product first zeroth parts construction uses the exists coord ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/RamifiedLatticeOperatorIdentity.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/RamifiedLatticeOperatorIdentity.lean#L75-L78

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]

theorem Formalism.LogVandermondeBounds.product_first_zeroth_parts.exists_coord_ne_zero {x : Fin r → k} (hx : x ≠ 0) : ∃ i, x i ≠ 0 := by sorry
