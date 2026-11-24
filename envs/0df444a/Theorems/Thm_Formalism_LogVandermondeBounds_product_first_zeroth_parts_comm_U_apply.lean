-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_comm_U_apply
-- name    : Formalism.LogVandermondeBounds.product_first_zeroth_parts.comm_U_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:28.246312+00:00
-- url     : https://prove2.me/theorems/e8f82138-7cbc-434f-b8ba-1b46306b8f45
-- title:
--   product first zeroth parts: comm U apply
-- statement:
--   The product first zeroth parts construction uses the comm U apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/RamifiedLatticeOperatorIdentity.lean#L65-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/RamifiedLatticeOperatorIdentity.lean#L65-L66

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

theorem Formalism.LogVandermondeBounds.product_first_zeroth_parts.comm_U_apply (c : kˣ) (ψ : (Fin r → k) → R) (f : Fin r → k) :
    opU (diaV c ψ) f = diaP c (opU ψ) f := by sorry
