-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_KK_gcd
-- name    : Formalism.HC.Der.Rd.KK_gcd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:10.536489+00:00
-- url     : https://prove2.me/theorems/80c44fe9-718e-490e-bdeb-f37410c5ab62
-- title:
--   Rd: KK gcd
-- statement:
--   The Rd construction uses the KK gcd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L392-L424
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L392-L424

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N]

theorem Formalism.HC.Der.Rd.KK_gcd (U : Subgroup (ZMod N)ˣ) {a b : ℕ} (ha : a ∣ N) (hb : b ∣ N) (h1 : ∀ u ∈ KK N a, u ∈ U)
    (h2 : ∀ u ∈ KK N b, u ∈ U) : ∀ u ∈ KK N (Nat.gcd a b), u ∈ U := by sorry
