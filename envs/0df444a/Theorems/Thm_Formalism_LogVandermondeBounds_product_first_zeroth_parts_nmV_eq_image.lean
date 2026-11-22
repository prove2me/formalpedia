-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_nmV_eq_image
-- name    : Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmV_eq_image
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:11.719797+00:00
-- url     : https://prove2.me/theorems/b78c2296-f5aa-41f9-b52e-37e708b2e483
-- title:
--   product first zeroth parts: nm V eq image
-- statement:
--   The product first zeroth parts construction uses the nm V eq image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/RamifiedLatticeOperatorIdentity.lean#L80-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/RamifiedLatticeOperatorIdentity.lean#L80-L89

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

theorem Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmV_eq_image (ψ : (Fin r → k) → R) {x : Fin r → k} (hx : x ≠ 0) :
    nmV ψ x = ∑ y ∈ univ.image (fun c : kˣ => ((c⁻¹ : kˣ) : k) • x), ψ y := by sorry
