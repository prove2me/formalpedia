-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_pairTwoLinear_apply
-- name    : Formalism.LogVandermondeBounds.product_first_zeroth_parts.pairTwoLinear_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:34.417873+00:00
-- url     : https://prove2.me/theorems/fc363850-c4b4-4bbf-b2f3-41f69333ad76
-- title:
--   product first zeroth parts: pair Two Linear apply
-- statement:
--   The product first zeroth parts construction uses the pair Two Linear apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/RamifiedLatticeOperatorIdentity.lean#L178-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/RamifiedLatticeOperatorIdentity.lean#L178-L178

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

theorem Formalism.LogVandermondeBounds.product_first_zeroth_parts.pairTwoLinear_apply (x y f : Fin r → k) : pairTwoLinear x y f = (pair f x, pair f y) := by sorry
