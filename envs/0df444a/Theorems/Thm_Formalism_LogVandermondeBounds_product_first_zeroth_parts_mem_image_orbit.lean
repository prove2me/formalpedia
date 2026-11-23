-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_mem_image_orbit
-- name    : Formalism.LogVandermondeBounds.product_first_zeroth_parts.mem_image_orbit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:40:00.417148+00:00
-- url     : https://prove2.me/theorems/a00e56f8-8db0-4c9c-8436-1736593ebd01
-- title:
--   product first zeroth parts: mem image orbit
-- statement:
--   The product first zeroth parts construction uses the mem image orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/RamifiedLatticeOperatorIdentity.lean#L91-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/RamifiedLatticeOperatorIdentity.lean#L91-L96

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

theorem Formalism.LogVandermondeBounds.product_first_zeroth_parts.mem_image_orbit {x : Fin r → k} (y : Fin r → k) :
    y ∈ univ.image (fun c : kˣ => ((c⁻¹ : kˣ) : k) • x) ↔ ∃ u : kˣ, u • x = y := by sorry
